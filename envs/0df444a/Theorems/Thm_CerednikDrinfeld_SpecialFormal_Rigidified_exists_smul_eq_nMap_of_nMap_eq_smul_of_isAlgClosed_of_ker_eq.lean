-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/b7050a84-3ea0-52f1-a1ba-fb3dcccb0428
-- title:
--   Zariski-local p-divisibility of an ηᵢ-section from a geometric fibre
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring map $\iota : \mathrm{Zp2}\,p \to O$ (where $\mathrm{Zp2}\,p = W(\mathbb F_{p^2})$), a formal $O_D$-module $\Phi$ over $O/pO$, a Noetherian commutative $\mathbb Z_p$-algebra $B$ with a ring map $\psi : O \to B$ and $p$ nilpotent in $B$, and a rigidified datum $t$ over $B$ (a formal $O_D$-module $t.X$ over $B$, an integer $n$, and a series $\rho$ over $B/pB$) which is admissible for $\iota,\psi$: $t.X$ is special for the structure map $\psi\circ\iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from $\bar\Phi$ to $\bar{t.X}$. Fix $i \in \{0,1\}$ and $f \in B$, write $B_f$ for the localisation of $B$ at the powers of $f$, and assume `hc`: the $0$- and $1$-graded pieces of the Cartier module of $t.X\otimes B_f$ are complementary, so that this Cartier module becomes a graded Cartier module datum $D_f$. Let $L : D_f.M \to D_f.\mathrm{NMod}$ be a canonical $L$-map (a Cartier $L$-map, i.e. $\sigma$-semilinear with $L(Vx) = [(\varpi x,0)]$ and $\lambda\circ L = F$, which moreover lifts along a surjection from a special Cartier module with no $p$-torsion), and let $z$ lie in $\eta_i$, that is in the intersection of the subgroup `eta` of $L$ with the image of $D_f.\mathrm{piece}\,i \times D_f.\mathrm{piece}\,i$ in $D_f.\mathrm{NMod}$. Let $K$ be an algebraically closed field which is a $\mathbb Z_p$-algebra and $g : B \to K$ a ring map compatible with the $\mathbb Z_p$-structures, with kernel the prime ideal of a point $x \in \operatorname{Spec} B$ and with $g(f)$ a unit; assume the base-changed datum $t.\mathrm{map}\,g$ is admissible for $\iota, g\circ\psi$, that the analogous complementarity `hc'` holds over $K$ localised away from $1$, giving $D_K$, and let $L'$ be a canonical $L$-map for $D_K$. Assume the formal group of $t.X\otimes B_f$ transported along the lift $B_f \to K$ of $g$ followed by $K \to K_{(1)}$ equals that of the fibre (`hXh`), that the resulting base-change map on Cartier modules commutes with Verschiebung and with $\varpi$, and that the image of $z$ under the induced map on $\mathrm{NMod}$ is $p\cdot y$ for some $y$ in the corresponding $\eta_i$ for $L'$. The conclusion asserts the existence of $f_0 \in B$ with $f_0 \notin x$, a complementarity `hc₀` over $B_{ff_0}$ with associated datum $D_{ff_0}$, a canonical $L$-map $L_0$ for it, an identification `hXr` of the formal group of $t.X\otimes B_f$ transported along $B_f \to B_{ff_0}$ with that of $t.X\otimes B_{ff_0}$, proofs that the associated base-change map commutes with Verschiebung and $\varpi$, and an element $z_0$ of $\eta_i$ for $L_0$ with $p\cdot z_0$ equal to the image of $z$ under the induced map $D_f.\mathrm{NMod} \to D_{ff_0}.\mathrm{NMod}$.
--
--   This is the spreading-out step in the study of the $\eta$-sections of a special formal $O_D$-module: $p$-divisibility of a section of $\eta_i$ at a geometric point of $\operatorname{Spec} B_f$ propagates to a Zariski neighbourhood $\operatorname{Spec} B_{ff_0}$ of that point. It is used in the proof that a section whose $p$-multiple lies in $\eta_i$ already lies in $\eta_i$, part of the Čerednik–Drinfeld uniformisation input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (i : Fin 2) (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung i)
    {K : Type} [Field K] [IsAlgClosed K] [Algebra ℤ_[p] K] (g : B →+* K)
    (hg : g.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] K)
    (x : PrimeSpectrum B) (hx : RingHom.ker g = x.asIdeal) (hgf : IsUnit (g f))
    (ht' : (t.map g).IsAdmissible ι (g.comp ψ))
    (hc' : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom (1 : K)))
    (L' : (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').M →+ (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').NMod) (hL' : (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').IsCanonicalLMap L')
    (hXh : (t.XS (Rigidified.awayHom f)).F.map ((algebraMap K (Rigidified.Baway (1 : K))).comp (IsLocalization.Away.lift f (g := g) hgf : Rigidified.Baway f →+* K)) = ((t.map g).XS (Rigidified.awayHom (1 : K))).F)
    (hbcV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung m) =
      (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hbcPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi m) =
      (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hdiv : ∃ y ∈ (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i,
      ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc') (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z = p • y) :
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
