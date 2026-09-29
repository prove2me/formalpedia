-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/b25898db-3467-5951-8231-937dac243d8e
-- title:
--   Local descent of an ηⱼ-class by p after localisation
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring homomorphism $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, a formal $O_D$-module $\Phi$ over $O/pO$, a Noetherian $\mathbb{Z}_p$-algebra $B$ with a ring homomorphism $\psi : O \to B$ such that $p$ is nilpotent in $B$, and a rigidified object $t$ over $B$ (a formal $O_D$-module $t.X$, an integer $t.n$, and a $2$-tuple of power series $t.\rho$ over $B/pB$) which is admissible for $\iota,\psi$: $t.X$ is special for the structure map $\psi\circ\iota$, has height $4$, and $t.\rho$ is an isogeny of height $4\,t.n$ from $\Phi$ base-changed to $B/pB$ to the reduction of $t.X$. Let $g : B \to S$ be a ring homomorphism into a reduced Noetherian ring $S$ with $p = 0$ in $S$, and assume `hc`, that the degree-$0$ and degree-$1$ graded pieces of the Cartier module of `t.XS g` are complementary; write $D$ for the resulting graded Cartier module data, with $M =$ the Cartier module of `(t.XS g).F`, Verschiebung $V$, the $\varpi$-action $\Pi$ and pieces indexed by $\mathrm{Fin}\,2$. Let $L : M \to N$ be a canonical Cartier $L$-map (Frobenius-semilinear, $L(Vx)$ the class of $(\Pi x,0)$, $\lambda\circ L = F$, together with the existence of the prescribed lift), let $j \in \mathrm{Fin}\,2$ and let $\gamma$ be a homogeneous $V$-basis: $\gamma_i$ lies in the $i$-th piece and every element of $M$ is uniquely $\sum_i [c_i]\gamma_i + Vy$. Assume $a \in S$ is a non-zero-divisor with $\Pi\gamma_j = [a]\gamma_{j+1} + Vx_j$ and $\Pi\gamma_{j+1} = Vx_j'$ for some $x_j, x_j' \in M$; let $z$ lie in the degree-$j$ part `etaPiece` of $\eta(L)$, let $x$ be a prime of $S$, and let $m_0$ be an element of the $(j+1)$-st piece with $\Pi m_0 = V m_0$ and $p\cdot m_0 = \lambda(z)$, written $m_0 = [c]\gamma_{j+1} + Vn$ with $c \in S$, $n \in M$, and suppose $a \in x$ implies $c \in x$. Then there exists $f_0 \in S \setminus x$ such that the analogous complementarity `hc₀` holds for the composite $B \to S \to S_{f_0}$, together with a canonical $L$-map $L_0$ for the corresponding data $D_0$ over $S_{f_0}$, an identification `hXr` of the base change of `(t.XS g).F` along $S \to S_{f_0}$ with `(t.XS _).F`, proofs that the induced additive map `baseChangeEq` on Cartier modules commutes with $V$ and with $\Pi$, and an element $z_0$ in the degree-$j$ part of $\eta(L_0)$ with $p\cdot z_0$ equal to the image of $z$ under the induced map $N \to N_0$.
--
--   This is the localised descent step in the analysis of the Cartier modules of special formal $O_D$-modules of height $4$ over reduced rings of characteristic $p$: starting from an $\eta$-class whose $\lambda$-image is $p$ times a $\Pi$-invariant element of the critical degree $j+1$, it produces, after inverting one element off a given prime, a $p$-th divisor of that class inside the degree-$j$ part of $\eta$. It is used in the proof of [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_teichmuller_smul_add_verschiebung`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_teichmuller_smul_add_verschiebung).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung.lean

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

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsReduced S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2) (γ : Fin 2 → ((t.XS g).toGradedCartierModuleData _ hc).M) (hγ : ((t.XS g).toGradedCartierModuleData _ hc).IsHomogeneousVBasis γ)
    (a : S) (ha : ∀ s : S, a * s = 0 → s = 0)
    (xj : ((t.XS g).toGradedCartierModuleData _ hc).M) (hnc : ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ j) = WittVector.teichmuller p a • γ (j + 1) + ((t.XS g).toGradedCartierModuleData _ hc).verschiebung xj)
    (xj' : ((t.XS g).toGradedCartierModuleData _ hc).M) (hcrit : ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ (j + 1)) = ((t.XS g).toGradedCartierModuleData _ hc).verschiebung xj')
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    (m₀ : ((t.XS g).toGradedCartierModuleData _ hc).M) (hm₀ : m₀ ∈ ((t.XS g).toGradedCartierModuleData _ hc).piece (j + 1)) (hinv₀ : ((t.XS g).toGradedCartierModuleData _ hc).varpi m₀ = ((t.XS g).toGradedCartierModuleData _ hc).verschiebung m₀)
    (hpm₀ : p • m₀ = ((t.XS g).toGradedCartierModuleData _ hc).lambda z)
    (c : S) (n : ((t.XS g).toGradedCartierModuleData _ hc).M) (hdig : m₀ = WittVector.teichmuller p c • γ (j + 1) + ((t.XS g).toGradedCartierModuleData _ hc).verschiebung n)
    (hcx : a ∈ x.asIdeal → c ∈ x.asIdeal) :
    ∃ (f₀ : S) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
      (L₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by sorry
