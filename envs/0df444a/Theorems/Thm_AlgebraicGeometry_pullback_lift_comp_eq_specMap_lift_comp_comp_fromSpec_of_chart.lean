-- Prove2me | Theorems.Thm_AlgebraicGeometry_pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart
-- name    : AlgebraicGeometry.pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/1bdc2c35-9ac2-51a3-8423-d545d3677651
-- title:
--   Points formula for an action on an affine chart
-- statement:
--   Let $K$ be a commutative ring, $A$ a scheme, $f \colon A \to \operatorname{Spec} K$ a morphism, and $H$ a commutative $K$-algebra; write $P$ for the pullback of $f$ along $\operatorname{Spec}$ of $K \to H$, with projections $p_1, p_2$. Assume given $\mathrm{act} \colon P \to A$ with $\mathrm{act} \circ f$-compatibility $\mathrm{act} \mathbin{≫} f = p_1 \mathbin{≫} f$, an affine open $V \subseteq A$, and the inclusion $p_1^{-1}V \le \mathrm{act}^{-1}V$. Sections over opens of $A$ and of $P$ are $K$-algebras via the maps induced by $f$ and by $p_1 \mathbin{≫} f$ on global sections. Then for every $K$-algebra isomorphism $\varepsilon \colon \Gamma(P, p_1^{-1}V) \cong \Gamma(A,V) \otimes_K H$ with $\varepsilon(p_1^{*}a) = a \otimes 1$ and $\varepsilon(p_2^{*}h) = 1 \otimes h$, every $K$-algebra map $\rho$ with $\rho(s) = \varepsilon(\mathrm{act}^{*}s)$ (restriction from $V$ to $p_1^{-1}V$), every $K$-algebra $T$ and $K$-algebra maps $\alpha \colon \Gamma(A,V) \to T$, $\chi \colon H \to T$: the canonical chart $\operatorname{Spec}\Gamma(A,V) \to A$ composed with $f$ equals $\operatorname{Spec}$ of $K \to \Gamma(A,V)$; and $\operatorname{Spec}\alpha$ followed by the chart, together with $\operatorname{Spec}\chi$, is compatible over $\operatorname{Spec} K$, so defines a map $\operatorname{Spec} T \to P$, whose composite with $\mathrm{act}$ equals $\operatorname{Spec}$ of $(\alpha \otimes \chi) \circ \rho$ followed by the chart.
--
--   This is the functor-of-points dictionary for an action morphism read on a single affine chart: $T$-valued points of $p_1^{-1}V \cong \operatorname{Spec}(\Gamma(A,V) \otimes_K H)$ correspond to pairs of $K$-algebra maps, and the action translates into the coaction $\rho$. It is used in the verification of the counit and coassociativity identities for the chart coaction in the relative group law on Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H]
    (act : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⟶ A)
    (hact : act ≫ f = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f)
    (V : A.Opens) (hV : IsAffineOpen V)
    (hle : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V ≤ act ⁻¹ᵁ V) :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens,
        Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
    ∀ (ε : Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H)
      (hε_fst : ∀ a : Γ(A, V),
        ε (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H))
      (hε_snd : ∀ h : H,
        ε (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
            ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) = (1 : Γ(A, V)) ⊗ₜ[K] h)
      (ρ : Γ(A, V) →ₐ[K] Γ(A, V) ⊗[K] H)
      (hρ : ∀ s : Γ(A, V), ρ s = ε ((act.appLE V ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) hle).hom s))
      (T : Type u) [CommRing T] [Algebra K T] (α : Γ(A, V) →ₐ[K] T) (χ : H →ₐ[K] T),
    hV.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Γ(A, V))) ∧
    ∃ hx : (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ hV.fromSpec) ≫ f =
        Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K H)),
      pullback.lift (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ hV.fromSpec) (Spec.map (CommRingCat.ofHom χ.toRingHom)) hx ≫ act =
        Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.lift α χ (fun _ _ => Commute.all _ _)).comp ρ).toRingHom) ≫
          hV.fromSpec := by sorry
