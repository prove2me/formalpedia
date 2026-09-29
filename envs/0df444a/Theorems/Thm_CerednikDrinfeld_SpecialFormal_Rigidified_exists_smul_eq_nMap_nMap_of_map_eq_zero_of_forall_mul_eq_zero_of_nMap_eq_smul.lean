-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/14a3eed1-8c06-5780-a299-b1a6fdce2983
-- title:
--   Pushing the p-divisibility datum along a map killing aⱼ₊₁
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring map $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, a formal $O_D$-module $\Phi$ over $O/pO$, a Noetherian $\mathbb{Z}_p$-algebra $B$ in which $p$ is nilpotent, a ring map $\psi : O \to B$, and a rigidified object $t$ over $B$ which is admissible for $(\iota,\psi)$, i.e. $t.X$ is special for the structure map $\psi\circ\iota$, has height $4$, and $t.\rho$ is an isogeny of height $4\,t.n$ from $\Phi$ reduced to $t.X$ reduced. Let $g : B \to S$ with $S$ reduced and Noetherian and $p = 0$ in $S$, and let `hc` assert that the graded pieces $0$ and $1$ of the Cartier module of `t.XS g` are complementary, so that the graded Cartier module data $D$ over $S$ is defined; let $L : D.M \to D.\mathrm{NMod}$ be a canonical $L$-map (a Cartier $L$-map admitting a lift from a special graded Cartier module over a $p$-torsion-free surjective cover), $j \in \{0,1\}$, and $z$ an element of the $j$-th $\eta$-piece of $L$. Let $x$ be a prime of $S$, $K$ an algebraically closed field and $k : S \to K$ a ring map with kernel the prime ideal of $x$; assume the corresponding grading `hc'` and canonical $L$-map $L'$ over $K$, an identification `hXh` of the formal group of `t.XS g` pushed along $k$ with that of `t.XS (k ∘ g)`, compatibility of the resulting base-change map with Verschiebung and with $\varpi$, and that the induced map on $N$-modules sends $z$ to $p\,y$ for some $y$ in the $j$-th $\eta$-piece of $L'$. Assume further a homogeneous $V$-basis $\gamma$ of $D$ (each $\gamma_i$ in the $i$-th piece, with unique decomposition $x = \sum_i [c_i]\gamma_i + V m$), elements $a_i \in S$ and $x_i \in D.M$ with $\varpi(\gamma_i) = [a_i]\,\gamma_{i+1} + V(x_i)$ for $i \in \{0,1\}$, where $[\cdot]$ is the Teichmüller lift. Finally let $h : S \to S'$ with $S'$ reduced and Noetherian, $x'$ a prime of $S'$ and $k' : S' \to K$ with $k'\circ h = k$ and kernel the prime ideal of $x'$, and suppose $h(a_{j+1}) = 0$ while $h(a_j)$ is a non-zero-divisor in $S'$. Then the grading condition holds along $h \circ g$, the formal group of `t.XS g` pushed along $h$ is that of `t.XS (h ∘ g)`, the associated base-change map commutes with Verschiebung and $\varpi$, and there exist $f_0 \in S'$ outside the prime ideal of $x'$, the grading condition and a canonical $L$-map $L_0$ over the localisation $S'_{f_0}$, identifications and compatibilities for the further base change along $S' \to S'_{f_0}$, and an element $z_0$ of the $j$-th $\eta$-piece of $L_0$ with $p\,z_0$ equal to the image of $z$ under the composite of the two induced maps on $N$-modules.
--
--   This is the transport step of the stratum descent in the Čerednik–Drinfeld theory of special formal $O_D$-modules: a $p$-divisibility datum over $S$, together with structure constants for a homogeneous $V$-basis, is pushed along a ring map that kills one structure constant and makes the other a non-zero-divisor, yielding the divisibility after a further localisation away from the given prime. It is used by [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul
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
    (hJ : h (a (j + 1)) = 0) (hnzd : ∀ s : S', h (a j) * s = 0 → s = 0) :
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
