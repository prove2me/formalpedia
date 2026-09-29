-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf
-- name    : AlgebraicGeometry.Scheme.Hom.app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/28e105e7-0eb3-5c4c-bf9f-6fa0b2d5074c
-- title:
--   Chart cocycle data pull back along a scheme morphism
-- statement:
--   Let $f : X \to Z$ be a morphism of schemes (over the zero universe), let $r$ be a natural number, let $V : \mathrm{Fin}\,r \to Z.\mathrm{Opens}$ be a finite family of open subsets of $Z$, and let $w$ assign to each pair $(i,j)$ a section $w_{ij} \in \Gamma(Z, V_i)$. Assume: (i) $w_{ii} = 1$ for every $i$; (ii) for all $i,j,k$ the cocycle identity holds after restriction to $V_i \cap V_j$, namely the image of $w_{ik}$ under the restriction $\Gamma(Z,V_i) \to \Gamma(Z, V_i \cap V_j)$ equals the product of the restriction of $w_{ij}$ along $V_i \cap V_j \le V_i$ with the restriction of $w_{jk}$ along $V_i \cap V_j \le V_j$; (iii) for all $i,j$ the basic open locus $Z_{w_{ij}} \subseteq V_i$ equals $V_i \cap V_j$. Then the pulled-back family, consisting of the opens $f^{-1}V_i$ of $X$ and the sections $f^\sharp_{V_i}(w_{ij}) \in \Gamma(X, f^{-1}V_i)$ obtained by applying the component of $f$ on sections over $V_i$, satisfies the same three conditions: $f^\sharp_{V_i}(w_{ii}) = 1$; the corresponding cocycle identity after restriction to $f^{-1}V_i \cap f^{-1}V_j$; and $X_{f^\sharp_{V_i}(w_{ij})} = f^{-1}V_i \cap f^{-1}V_j$.
--
--   This is the statement that the standard chart datum of a line bundle on projective space — a family of opens together with transition units whose non-vanishing loci are exactly the pairwise intersections — is preserved by pullback along an arbitrary morphism of schemes; no affineness or finiteness condition on $f$ is imposed. It is used in the construction of immersions into projective space, being cited by [`AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`](thm.html#AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj) and by [`AlgebraicGeometry.exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing`](thm.html#AlgebraicGeometry.exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.Hom.app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf
    {X Z : Scheme.{0}} (f : X ⟶ Z) {r : ℕ} (V : Fin r → Z.Opens) (w : ∀ i j : Fin r, Γ(Z, V i))
    (hW1 : ∀ i, w i i = 1)
    (hW2 : ∀ i j k : Fin r,
      Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j) :
    (∀ i : Fin r, f.app (V i) (w i i) = 1) ∧
    (∀ i j k : Fin r,
      X.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V i)).op (f.app (V i) (w i k)) =
        X.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V i)).op (f.app (V i) (w i j)) *
          X.presheaf.map (homOfLE (inf_le_right : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V j)).op (f.app (V j) (w j k))) ∧
    (∀ i j : Fin r, X.basicOpen (f.app (V i) (w i j)) = f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j) := by sorry
