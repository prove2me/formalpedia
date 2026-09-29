-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_nMap_of_map_eq_zero_of_nMap_eq_smul
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_nMap_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a6ebecd8-b09d-52f4-89c4-466f3ff20d09
-- title:
--   Transport of a p-divisibility datum along a map killing aⱼ
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring map $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, a formal $O_D$-module $\Phi$ over $O/pO$, a Noetherian $\mathbb{Z}_p$-algebra $B$ with $\psi : O \to B$ and $p$ nilpotent in $B$, and a rigidified object $t$ over $B$ (a formal $O_D$-module $t.X$, an integer $n$, and a series $\rho$ over $B/pB$) which is admissible for $\iota,\psi$: $t.X$ is special for the structure map $\psi\circ\iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from $\Phi$ base changed along $\psi$ to the reduction of $t.X$. Let $g : B \to S$ with $S$ reduced and Noetherian and $p = 0$ in $S$, and assume the degree-$0$ and degree-$1$ graded pieces of the Cartier module of `t.XS g` are complementary, so that the graded Cartier module data $D$ with its Verschiebung $V$, Frobenius and $\varpi$-action is defined; let $L : D.M \to D.NMod$ be a canonical $L$-map, $j \in \{0,1\}$, and $z$ an element of the $j$-th $\eta$-piece of $L$ (the intersection of $\eta(L)$ with the $j$-th graded piece of $D.NMod$). Let $x$ be a prime of $S$ and $k : S \to K$ a map to an algebraically closed field with kernel the prime $x$, assume the corresponding grading over $K$ holds, let $L'$ be a canonical $L$-map for the data $D'$ attached to `t.XS (k.comp g)`, and assume the formal group law of `t.XS g` base changed along $k$ equals that of `t.XS (k.comp g)`, with the induced base-change map on Cartier modules commuting with $V$ and with $\varpi$; assume moreover that the image of $z$ under the induced map $D.NMod \to D'.NMod$ is $p\cdot y$ for some $y$ in the $j$-th $\eta$-piece of $L'$. Let $\gamma$ be a homogeneous $V$-basis of $D$ (with $\gamma_i$ in the $i$-th piece and every element uniquely of the form $\sum_i [c_i]\gamma_i + V(m)$), and let $a : \{0,1\} \to S$, $xs : \{0,1\} \to D.M$ satisfy the structure equations $\varpi(\gamma_i) = [a_i]\,\gamma_{i+1} + V(xs_i)$, where $[\,\cdot\,]$ is the Teichmüller lift. Finally let $h : S \to S'$ with $S'$ reduced and Noetherian, $x'$ a prime of $S'$, and $k' : S' \to K$ with $k'\circ h = k$ and kernel the prime $x'$, and suppose $h(a_j) = 0$. The conclusion asserts the existence of: the grading along $h\circ g$; an equality of the formal group law of `t.XS g` base changed along $h$ with that of `t.XS (h.comp g)`, together with compatibility of the resulting base-change map with $V$ and $\varpi$; an element $f_0 \in S'$ outside $x'$; the grading along the composite of $h\circ g$ with $S' \to S'_{f_0}$; a canonical $L$-map $L_0$ for the data over the localisation $S'_{f_0}$; an equality of formal group laws and the corresponding compatibilities with $V$ and $\varpi$ for the localisation map; and an element $z_0$ of the $N$-module over $S'_{f_0}$ lying in the $j$-th $\eta$-piece of $L_0$ with $p\cdot z_0$ equal to the image of $z$ under the composite of the induced maps along $h$ and along $S' \to S'_{f_0}$.
--
--   This is a transport step in the analysis of the strata of the moduli problem of special formal $O_D$-modules: a datum expressing $p$-divisibility of $z$ in the $\eta$-piece over a geometric point is pushed forward along a ring map $h$ which annihilates the structure constant $a_j$, at the cost of passing to a localisation $S'_{f_0}$ away from the chosen prime $x'$. It is used in the proof of [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_nMap_of_map_eq_zero_of_nMap_eq_smul.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_nMap_eq_smul
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
      ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z = p • y)
    (γ : Fin 2 → ((t.XS g).toGradedCartierModuleData _ hc).M) (hγ : ((t.XS g).toGradedCartierModuleData _ hc).IsHomogeneousVBasis γ)
    (a : Fin 2 → S) (xs : Fin 2 → ((t.XS g).toGradedCartierModuleData _ hc).M)
    (hstr : ∀ i : Fin 2, ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ i) = WittVector.teichmuller p (a i) • γ (i + 1) + ((t.XS g).toGradedCartierModuleData _ hc).verschiebung (xs i))
    {S' : Type} [CommRing S'] [IsReduced S'] [IsNoetherianRing S'] (h : S →+* S')
    (x' : PrimeSpectrum S') (k' : S' →+* K) (hk' : k'.comp h = k) (hker' : RingHom.ker k' = x'.asIdeal)
    (hJ : h (a j) = 0) :
    ∃ (hch : t.IsGradedS ι ψ (h.comp g))
      (hXh' : (t.XS g).F.map h = (t.XS (h.comp g)).F)
      (hhV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh' (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh' m))
      (hhPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh' (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh' m))
      (f₀ : S') (_ : f₀ ∉ x'.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S' (Localization.Away f₀)).comp (h.comp g)))
      (L₀ : ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS (h.comp g)).F.map (algebraMap S' (Localization.Away f₀)) = (t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (h.comp g)).toGradedCartierModuleData _ hch).verschiebung m) =
        ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (h.comp g)).toGradedCartierModuleData _ hch).varpi m) =
        ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS (h.comp g)).toGradedCartierModuleData _ hch).nMap ((t.XS ((algebraMap S' (Localization.Away f₀)).comp (h.comp g))).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi
          (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (h.comp g)).toGradedCartierModuleData _ hch) (MvFormalGroup.CartierModule.baseChangeEq _ hXh') hhV hhPi z) := by sorry
