-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_teichmuller_smul_add_verschiebung
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_teichmuller_smul_add_verschiebung
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/3ffc04c3-8958-520e-8219-776dd73ea35d
-- title:
--   Spreading out p-divisibility in ηⱼ at a non-critical index
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring with a ring homomorphism $\iota\colon \mathbb{W}(\mathbb{F}_{p^2})\to O$, and $\Phi$ a formal $O_D$-module over $O/pO$. Let $B$ be a Noetherian commutative $\mathbb{Z}_p$-algebra with $\psi\colon O\to B$ and $p$ nilpotent in $B$, and let $t=(X,n,\rho)$ be a rigidified object over $B$ that is admissible for $\iota,\psi$ (namely $X$ is special for the structure map $\psi\circ\iota$, of height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$). Let $g\colon B\to S$ with $S$ reduced, Noetherian and $p=0$ in $S$, and assume `t.IsGradedS ι ψ g`, i.e. the two graded pieces of degree $0$ and $1$ of the Cartier module of $(t.XS g).F$ with respect to $jS\,\iota\,\psi\,g$ are complementary submodules; write $D$ for the resulting graded Cartier module data, with Frobenius, Verschiebung $V$, the operator $\varpi$ and the two pieces. Let $L\colon D.M\to D.NMod$ be a canonical $L$-map, $j\in\{0,1\}$, and $\gamma$ a homogeneous $V$-basis of $D$ (each $\gamma_i$ in the piece of degree $i$, every element uniquely of the form $\sum_i [c_i]\gamma_i + V m$). Suppose $a\in S$ is a non-zero-divisor and $\varpi\gamma_j = [a]\cdot\gamma_{j+1} + V x_j$ for some $x_j$, while $\varpi\gamma_{j+1}=V x_j'$ for some $x_j'$. Let $z$ lie in the degree-$j$ part `etaPiece L … j` of $D.NMod$. Let $x$ be a prime of $S$, $K$ an algebraically closed field and $k\colon S\to K$ a ring homomorphism with kernel the prime ideal of $x$, together with the corresponding grading hypothesis over $K$ for $k\circ g$, a canonical $L$-map $L'$ there, an identification `hXh` of the formal group $(t.XS g).F$ pushed along $k$ with $(t.XS (k\circ g)).F$, and the hypotheses that the associated base-change map on Cartier modules commutes with $V$ and with $\varpi$. Assume that the induced map `nMap` sends $z$ to $p\cdot y$ for some $y$ in the degree-$j$ eta piece of $L'$. Then there exist $f_0\in S$ not in the prime ideal of $x$, a grading hypothesis over $\mathrm{Localization.Away}\,f_0$ for $(\mathrm{algebraMap})\circ g$, a canonical $L$-map $L_0$ there, an identification `hXr` of the formal group after localisation together with the commutation of the base-change map with $V$ and $\varpi$, and an element $z_0$ of the degree-$j$ eta piece of $L_0$ such that $p\cdot z_0$ equals the image of $z$ under the corresponding map `nMap` to the localised data.
--
--   This is the non-critical-index case of the descent step in the Cartier-theoretic analysis of special formal $O_D$-modules underlying the Čerednik–Drinfeld uniformisation: $p$-divisibility of a section of $\eta_j$ verified at a geometric point of a reduced base spreads to a Zariski-open neighbourhood of that point. It feeds the statement [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul), where such local divisibility statements are glued.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_teichmuller_smul_add_verschiebung.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_teichmuller_smul_add_verschiebung
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
    {K : Type} [Field K] [IsAlgClosed K] (k : S →+* K) (hk : RingHom.ker k = x.asIdeal)
    (hc' : t.IsGradedS ι ψ (k.comp g))
    (L' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').M →+ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').NMod) (hL' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').IsCanonicalLMap L')
    (hXh : (t.XS g).F.map k = (t.XS (k.comp g)).F)
    (hbcV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hbcPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hdiv : ∃ y ∈ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').etaPiece L' hL'.isCartierLMap.map_verschiebung j,
      ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z = p • y) :
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
