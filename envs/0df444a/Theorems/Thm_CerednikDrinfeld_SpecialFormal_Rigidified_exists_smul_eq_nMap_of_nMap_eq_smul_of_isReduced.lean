-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/3d2f5838-8529-5782-90f3-ff8f2c213412
-- title:
--   Zariski-local p-divisibility in ηⱼ over a reduced base
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring map $\iota\colon \mathbb{W}(\mathbb{F}_{p^2}) \to O$ (here $\mathbb{W}(\mathbb{F}_{p^2})$ is `Zp2 p`), and a formal $\mathcal{O}_D$-module $\Phi$ over $O/pO$. Let $B$ be a Noetherian commutative $\mathbb{Z}_p$-algebra with $p$ nilpotent in $B$, let $\psi\colon O \to B$, and let $t$ be a rigidified object over $B$ — a formal $\mathcal{O}_D$-module $t.X$ over $B$, an integer $t.n$ and a system $t.\rho$ of power series over $B/pB$ — which is admissible: $t.X$ is special for $\psi \circ \iota$, has height $4$, and $t.\rho$ is an isogeny of height $4\,t.n$ from $\Phi$ base-changed along $\psi$ to the reduction of $t.X$. Let $g\colon B \to S$ with $S$ reduced and Noetherian and $p = 0$ in $S$, and let `hc` assert that the two graded pieces of the Cartier module of `t.XS g` are complementary, so that the graded Cartier module data $D =$ `(t.XS g).toGradedCartierModuleData _ hc` is defined: its underlying module is the Cartier module of the formal group law of `t.XS g` over the Witt vectors of $S$, with Frobenius, Verschiebung, the operator $\varpi$ and the two homogeneous pieces. Let $L\colon D.M \to D.\mathrm{NMod}$ be a canonical $L$-map, $j \in \{0,1\}$, and $z$ an element of the degree-$j$ part `etaPiece` of $L$. Let $x$ be a prime of $S$ and $k\colon S \to K$ a map to an algebraically closed field with kernel $x$, with a grading `hc'` and a canonical $L'$ for the fibre `t.XS (k.comp g)`, an identification `hXh` of the base change of the formal group law along $k$ with that of `t.XS (k.comp g)`, and the compatibility of the induced base-change map of Cartier modules with Verschiebung and with $\varpi$. Assume that the induced map `nMap` sends $z$ to $p \cdot y$ for some $y$ in the degree-$j$ `etaPiece` of $L'$. Then there exist $f_0 \in S$ outside $x$, a grading `hc₀` and a canonical $L_0$ for `t.XS` over the localisation $S[1/f_0]$, an identification `hXr` of the base change of the formal group law along $S \to S[1/f_0]$, the corresponding Verschiebung- and $\varpi$-compatibilities, and an element $z_0$ in the degree-$j$ `etaPiece` of $L_0$ with $p \cdot z_0$ equal to the image of $z$ under the induced map `nMap` to the localisation.
--
--   This is the descent step which spreads $p$-divisibility of a section of $\eta_j$ from a single geometric fibre to a Zariski neighbourhood of the corresponding prime, over a reduced Noetherian base of characteristic $p$, in the Cartier-theoretic analysis of special formal $\mathcal{O}_D$-modules underlying the Čerednik–Drinfeld uniformisation. It is used to obtain the version of the statement phrased directly in terms of an algebraically closed residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsReduced S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2)
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
