-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/f319fb2a-c13b-584e-a116-c93a841fc6ba
-- title:
--   At a node, varpi-pull-back a coboundary forces γ a coboundary
-- statement:
--   Let $q$ be a prime and $k$ an algebraically closed field of characteristic $q$, and let $j_0\colon W(\mathbb F_{q^2})\to k$ be a ring homomorphism. Let $X_0$ be a special formal $\mathcal O_D$-module over $k$ relative to $j_0$, that is: a two-dimensional commutative formal group law $F$ over $k$ together with an action $a\mapsto \mathrm{act}(a)$ of $W(\mathbb F_{q^2})$ by endomorphisms of $F$ and an endomorphism $\varpi$ of $F$ with $\varpi\circ\varpi=\mathrm{act}(q)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$ for the Frobenius $\sigma$, such that the two eigen-submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$ of $\mathrm{Lie}\,X_0$ (where $\mathrm{act}(a)$ acts by $j_0(a)$, resp. by $j_0(\sigma a)$, for all $a$) are complementary and invertible, and the kernel of $\mathrm{act}(q)$ has degree $q^4$ (height $4$). Assume the node condition: the linear part of $\varpi$, viewed as a matrix acting on $\mathrm{Lie}\,X_0$, annihilates both $\mathrm{lieZero}$ and $\mathrm{lieOne}$. Let $\gamma$ be a symmetric additive $2$-cocycle for $F$ in four variables (zero constant term, invariant under interchanging the two groups of two variables, and satisfying the additive cocycle identity for $F$), and let $g$ be a power series in two variables whose constant term and all linear coefficients vanish. Writing $\mathrm{pull}(\varphi,\Gamma)$ for the substitution of $\varphi$ into each of the two groups of variables of $\Gamma$, suppose $\mathrm{pull}(\varpi,\gamma)=\partial g$, where $\partial g = g(F(X,Y))-g(X)-g(Y)$. Then $\gamma=\partial b$ for some power series $b$ in two variables with zero constant term.
--
--   This is the node (double-point) injectivity step in the study of symmetric additive extensions of the formal group of a special formal $\mathcal O_D$-module arising in the Cherednik–Drinfeld uniformisation: where the linear part of the uniformiser kills the whole Lie algebra, the linear read-out of the series $g$ with $\varpi^*\gamma=\partial g$ detects whether $\gamma$ is a coboundary. It is used in the construction of isomorphisms of such modules over the node and in the accompanying decomposition of coboundaries by eigentype.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hnode₀ : ∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (hnode₁ : ∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hγ : X₀.F.IsSymmTwoCocycle γ)
    (g : MvPowerSeries (Fin 2) k) (hg0 : MvPowerSeries.constantCoeff g = 0)
    (hglin : ∀ m, MvPowerSeries.coeff (Finsupp.single m 1) g = 0) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    pull X₀.varpi γ = X₀.F.addCoboundary g →
    ∃ b : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff b = 0 ∧ γ = X₀.F.addCoboundary b := by sorry
