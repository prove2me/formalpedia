-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_forall_nMap_baseChange_eq_zero
-- name    : CerednikDrinfeld.FormalODModule.eq_zero_of_forall_nMap_baseChange_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/3279e558-e022-5e3b-b793-5370998fd422
-- title:
--   Vanishing in N(M) detected by jointly injective base changes
-- statement:
--   Fix a prime $p$, a commutative ring $S$ and a ring homomorphism $j\colon W(\mathbb{F}_{p^2})\to S$, and let $X$ be a formal $\mathcal{O}_D$-module over $S$: a commutative $2$-dimensional formal group law $X.F$ together with an additive multiplicative action of $W(\mathbb{F}_{p^2})$ by endomorphisms of $X.F$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ a=\sigma(a)\circ\varpi$. Let $M=\mathrm{CartierModule}\,p\,X.F$, and let $\gamma\colon \mathrm{Fin}\,2\to M$ satisfy `IsHomogeneousVBasis`, i.e. $\gamma_i$ lies in the $i$-th graded piece — the set of $f$ with $a_c\cdot f=[j(c)^{p^{i}}]f$ for every $c\in\mathbb{F}_{p^2}$ — and the matrix of tangent coordinates $(\mathrm{tangent}(\gamma_i)_k)$ has unit determinant; assume further that the graded pieces for $n=0$ and $n=1$ are complementary additive subgroups of $M$, giving the graded Cartier module datum $D=X.\mathrm{toGradedCartierModuleData}\,j\,hc$ with $V=$ the integral Verschiebung and $\Pi=$ the action of $\varpi$. Let $(K_\alpha)_{\alpha\in\iota}$ be a family of commutative rings and $\varphi_\alpha\colon S\to K_\alpha$ ring homomorphisms that are jointly injective ($\varphi_\alpha(s)=0$ for all $\alpha$ forces $s=0$), such that the graded pieces of the base-changed module $X.\mathrm{map}\,\varphi_\alpha$ along $\varphi_\alpha\circ j$ are again complementary, giving data $D_\alpha$. Let $\mathrm{bc}_\alpha\colon M\to \mathrm{CartierModule}\,p\,(X.\mathrm{map}\,\varphi_\alpha).F$ be additive maps assumed equal to `CartierModule.baseChange` along $\varphi_\alpha$ and assumed to commute with $V$ and with $\Pi$. Then for $z$ in $D.\mathrm{NMod}$, the quotient of $D.M\times D.\mathrm{Sigma}$ (the Frobenius twist of $D.M$) by the submodule `nRel`, if the induced map $D.\mathrm{nMod}\to D_\alpha.\mathrm{nMod}$ given by $\mathrm{nMap}$ kills $z$ for every $\alpha$, then $z=0$.
--
--   This is the joint-injectivity step for the functor $M\mapsto N(M)=(M\oplus M^\sigma)/\{(Vm,-\Pi m)\}$ attached to the Cartier module of a special formal $\mathcal{O}_D$-module, allowing vanishing in $N(M)$ over $S$ to be tested after base change along a separating family of ring homomorphisms. It is used in the analysis of the $\eta$-part of $N(M)$ over reduced rings, via the statement that the graded Cartier module datum attached to $X$ with a homogeneous $V$-basis is special.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_forall_nMap_baseChange_eq_zero.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
  MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.FormalODModule.eq_zero_of_forall_nMap_baseChange_eq_zero
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    {ι : Type} (K : ι → Type) [∀ α, CommRing (K α)] (φ : ∀ α, S →+* K α)
    (hinj : ∀ s : S, (∀ α, φ α s = 0) → s = 0)
    (hcK : ∀ α, IsCompl ((X.map (φ α)).gradedPiece ((φ α).comp j) 0) ((X.map (φ α)).gradedPiece ((φ α).comp j) 1))
    (bc : ∀ α, CartierModule p X.F →+ CartierModule p (X.map (φ α)).F)
    (hbc : ∀ α, bc α = CartierModule.baseChange (φ α))
    (hbcV : ∀ α x, bc α ((X.toGradedCartierModuleData j hc).verschiebung x) = ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)).verschiebung (bc α x))
    (hbcPi : ∀ α x, bc α ((X.toGradedCartierModuleData j hc).varpi x) = ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)).varpi (bc α x))
    (z : (X.toGradedCartierModuleData j hc).NMod)
    (hz : ∀ α, (X.toGradedCartierModuleData j hc).nMap ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)) (bc α) (hbcV α) (hbcPi α) z = 0) :
    z = 0 := by sorry
