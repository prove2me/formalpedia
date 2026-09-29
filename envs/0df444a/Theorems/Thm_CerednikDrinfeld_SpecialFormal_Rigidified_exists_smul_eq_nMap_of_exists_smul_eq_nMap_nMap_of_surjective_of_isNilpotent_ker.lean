-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/d1fe2ef5-8035-526b-b810-65942848274a
-- title:
--   Local p-divisibility of η-sections along nilpotent thickenings
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring homomorphism $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, a formal $O_D$-module $\Phi$ over $O/pO$, a Noetherian commutative $\mathbb{Z}_p$-algebra $B$ with $\psi : O \to B$ and $p$ nilpotent in $B$, a rigidified object $t$ over $B$ (a formal $O_D$-module over $B$, a level $n$, and a rigidification series over $B/pB$), an index $i \in \{0,1\}$ and an element $f \in B$. Over the localisation $B_f$ it is assumed that the graded pieces $0$ and $1$ of the Cartier module of $t.XS$ for the grading homomorphism attached to $\iota,\psi$ are complementary submodules (the hypothesis `IsGradedS`), that $L$ is a canonical Cartier $L$-map on the resulting graded Cartier module datum — i.e. $L$ is $\sigma$-semilinear, sends $V x$ to the class of $(\varpi x, 0)$, satisfies $\lambda \circ L = F$, and is pulled back from a Cartier $L$-map on a special graded Cartier module over a $p$-torsion-free surjective cover — and that $z$ lies in $\eta(L) \cap N_i$, the $i$-th graded piece of $\eta$ in $N$. Let $x$ be a prime of $B$. Let further $q : B_f \to S$ be a surjective ring homomorphism with nilpotent kernel, equipped with a grading hypothesis and a canonical $L$-map $L_S$ over $S$, together with the identification $\mathrm{hXS}$ of the base change along $q$ of the formal group of $t.XS$ over $B_f$ with that of $t.XS$ over $S$, and the assumptions that the induced additive base-change map on Cartier modules commutes with Verschiebung and with $\varpi$; let $x_S$ be a prime of $S$ whose contraction along $B \to B_f \to S$ is $x$. Assume $p$-divisibility Zariski-locally at $x_S$ after this reduction: there exist $f_0' \notin x_S$, a grading, a canonical $L$-map $L_0'$, a pinning of the formal group and compatibilities of the base change along $S \to S_{f_0'}$ with Verschiebung and $\varpi$, and an element $z_0'$ of the $i$-th graded piece of $\eta(L_0')$ over $S_{f_0'}$ with $p \cdot z_0'$ equal to the image of $z$ under the composite of the two induced maps on $N$. The conclusion is the corresponding statement over $B$: there exist $f_0 \in B$ with $f_0 \notin x$, a grading over $B_{f f_0}$, a canonical $L$-map $L_0$, an identification of the base change along $B_f \to B_{f f_0}$ of the formal group of $t.XS$ with the one over $B_{f f_0}$, compatibilities of the induced Cartier-module map with Verschiebung and $\varpi$, and an element $z_0$ of the $i$-th graded piece of $\eta(L_0)$ with $p \cdot z_0$ equal to the image of $z$ under the induced map on $N$.
--
--   This is the descent step expressing that the subgroup $\eta$ and its graded pieces are insensitive to a nilpotent thickening of the base, in the Zariski-local form needed for $p$-divisibility of sections; it transports local $p$-divisibility from a quotient $S$ of $B_f$ by a nilpotent ideal back to $B_f$ itself. It is used in [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq), where one takes $S = B_f$ modulo its nilradical and combines this with the divisibility statement over a reduced base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B)
    (i : Fin 2) (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung i)
    (x : PrimeSpectrum B)

    {S : Type} [CommRing S] (q : Rigidified.Baway f →+* S) (hq : Function.Surjective q) (hqI : IsNilpotent (RingHom.ker q))
    (hcS : t.IsGradedS ι ψ (q.comp (Rigidified.awayHom f)))
    (LS : ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).M →+ ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).NMod) (hLS : ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).IsCanonicalLMap LS)
    (hXS : (t.XS (Rigidified.awayHom f)).F.map q = (t.XS (q.comp (Rigidified.awayHom f))).F)
    (hSV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXS (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXS m))
    (hSP : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXS (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXS m))
    (xS : PrimeSpectrum S) (hxS : Ideal.comap (q.comp (Rigidified.awayHom f)) xS.asIdeal = x.asIdeal)

    (hred : ∃ (f₀' : S) (_ : f₀' ∉ xS.asIdeal) (hc₀' : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f))))
      (L₀' : ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').M →+ ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').NMod) (hL₀' : ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').IsCanonicalLMap L₀')
      (hXr' : (t.XS (q.comp (Rigidified.awayHom f))).F.map (algebraMap S (Localization.Away f₀')) = (t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).F)
      (hrV' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr' (((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr' m))
      (hrPi' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr' (((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr' m))
      (z₀' : ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').NMod),
      z₀' ∈ ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').etaPiece L₀' hL₀'.isCartierLMap.map_verschiebung i ∧
        p • z₀' = ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hXr') hrV' hrPi'
          (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS) (MvFormalGroup.CartierModule.baseChangeEq _ hXS) hSV hSP z)) :
    ∃ (f₀ : B) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ (Rigidified.awayHom (f * f₀)))
      (L₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).M →+ ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS (Rigidified.awayHom f)).F.map (IsLocalization.Away.awayToAwayRight f f₀ : Rigidified.Baway f →+* Rigidified.Baway (f * f₀)) = (t.XS (Rigidified.awayHom (f * f₀))).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung i ∧
        p • z₀ = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by sorry
