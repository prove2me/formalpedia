-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant
-- name    : AlgebraicGeometry.Scheme.exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/d45644be-9086-5675-8dfb-8385968122d1
-- title:
--   Descent of an invariant cocycle chart datum along q
-- statement:
--   Let $X,Y$ be schemes, $\Gamma$ a group and $\rho:\Gamma\to\operatorname{Aut}X$ a homomorphism, and let $q:X\to Y$ be a morphism such that: $(\rho\gamma)$ followed by $q$ equals $q$ for all $\gamma$; the underlying map $q.\mathrm{base}$ is surjective; for every open $V\subseteq Y$ the map on sections $q.\mathrm{app}\,V:\Gamma(Y,V)\to\Gamma(X,q^{-1}V)$ is injective with image exactly the sections fixed by every $(\rho\gamma)$ acting on $\Gamma(X,q^{-1}V)$ (via the restriction map of $\rho\gamma$ from $q^{-1}V$ to $q^{-1}V$, legitimate since $q$ is invariant); and every affine open $U\subseteq X$ with $(\rho\gamma)^{-1}U=U$ for all $\gamma$ equals $q^{-1}V$ for some affine open $V\subseteq Y$. Let $r\in\mathbb{N}$ and $U:\mathrm{Fin}\,r\to X.\mathrm{Opens}$ with each $U_i$ affine, $(\rho\gamma)^{-1}U_i=U_i$, and $\bigsqcup_i U_i=\top$; let $w_{ij}\in\Gamma(X,U_i)$ satisfy $w_{ii}=1$, $w_{ik}=w_{ij}\,w_{jk}$ after restriction to $U_i\cap U_j$, $X.\mathrm{basicOpen}(w_{ij})=U_i\cap U_j$, and invariance of each $w_{ij}$ under every $\rho\gamma$. Then there exist affine opens $V_i\subseteq Y$ and sections $v_{ij}\in\Gamma(Y,V_i)$ with $q^{-1}V_i=U_i$, $\bigsqcup_i V_i=\top$, $v_{ii}=1$, the same cocycle identity on $V_i\cap V_j$, $Y.\mathrm{basicOpen}(v_{ij})=V_i\cap V_j$, and $q^{\sharp}v_{ij}=w_{ij}$ (for any proof that $U_i\le q^{-1}V_i$).
--
--   This is the descent step in the construction of a quotient of a quasi-projective scheme by a finite group action: an invariant covering by affine opens together with an invariant unit cocycle whose non-vanishing loci are the pairwise intersections is transported from $X$ to $Y$. It is used by [`AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj`](thm.html#AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj), where such a datum on $Y$ yields an immersion into projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant
    (X Y : Scheme.{0}) (Γ : Type) [Group Γ] (ρ : Γ →* Aut X)
    (q : X ⟶ Y) (hq : ∀ γ : Γ, (ρ γ).hom ≫ q = q) (hsurj : Function.Surjective q.base)
    (hinj : ∀ V : Y.Opens, Function.Injective (q.app V))
    (hrange : ∀ V : Y.Opens, Set.range (q.app V) =
      {t | ∀ γ : Γ, (ρ γ).hom.appLE (q ⁻¹ᵁ V) (q ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hq γ]) t = t})
    (hdesc : ∀ U : X.Opens, IsAffineOpen U → (∀ γ : Γ, (ρ γ).hom ⁻¹ᵁ U = U) → ∃ V : Y.Opens, IsAffineOpen V ∧ q ⁻¹ᵁ V = U)
    (r : ℕ) (U : Fin r → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i))
    (hinv : ∀ (γ : Γ) (i : Fin r), (ρ γ).hom ⁻¹ᵁ U i = U i) (hcov : (⨆ i, U i) = ⊤)
    (w : ∀ i j : Fin r, Γ(X, U i)) (hw1 : ∀ i, w i i = 1)
    (hw2 : ∀ i j k : Fin r,
      X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
        X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
          X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k))
    (hw3 : ∀ i j : Fin r, X.basicOpen (w i j) = U i ⊓ U j)
    (hw4 : ∀ (γ : Γ) (i j : Fin r), (ρ γ).hom.appLE (U i) (U i) (le_of_eq (hinv γ i).symm) (w i j) = w i j) :
    ∃ (V : Fin r → Y.Opens) (v : ∀ i j : Fin r, Γ(Y, V i)),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, q ⁻¹ᵁ V i = U i) ∧ (⨆ i, V i) = ⊤ ∧
      (∀ i, v i i = 1) ∧
      (∀ i j k : Fin r,
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (v i k) =
          Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (v i j) *
            Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (v j k)) ∧
      (∀ i j : Fin r, Y.basicOpen (v i j) = V i ⊓ V j) ∧
      (∀ (i j : Fin r) (e : U i ≤ q ⁻¹ᵁ V i), q.appLE (V i) (U i) e (v i j) = w i j) := by sorry
