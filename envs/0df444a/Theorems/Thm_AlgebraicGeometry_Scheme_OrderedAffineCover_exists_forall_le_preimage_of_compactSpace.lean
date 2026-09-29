-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/e2794678-dc8b-5369-a316-59f6caf46f3a
-- title:
--   Common affine refinement of finitely many covers along morphisms
-- statement:
--   Let $Y$ be a scheme whose underlying topological space is compact (quasi-compact), let $n$ be a natural number, let $X : \mathrm{Fin}\,n \to \mathbf{Sch}$ be a finite family of schemes, let $h_j \colon Y \to X_j$ be a morphism of schemes for each $j$, and for each $j$ let $\mathcal U_j$ be an ordered affine cover of $X_j$, that is: a type $(\mathcal U_j).\iota$ equipped with a finite type structure and a linear order, a family of opens $(\mathcal U_j).U \colon (\mathcal U_j).\iota \to (X_j)^{\mathrm{op}}$ of $X_j$, each of which is an affine open, whose supremum is the whole of $X_j$. The assertion is that there exist an ordered affine cover $\mathcal W$ of $Y$ (so a finite linearly ordered index type $\mathcal W.\iota$ together with affine opens $\mathcal W.U\,w$ of $Y$ covering $Y$) and, for each $j$, a map $\lambda_j \colon \mathcal W.\iota \to (\mathcal U_j).\iota$, such that for every $j \in \mathrm{Fin}\,n$ and every $w \in \mathcal W.\iota$ one has the inclusion of opens $\mathcal W.U\,w \le h_j^{-1}\bigl((\mathcal U_j).U(\lambda_j w)\bigr)$.
--
--   This is the standard refinement lemma for Čech computations: a quasi-compact scheme admits a single finite ordered affine open cover which refines, simultaneously and along finitely many given morphisms, finitely many prescribed affine covers of the targets. Specialising to $X_j = Y$ with $h_j$ the identity gives common refinements of several covers of $Y$ itself; it is used in the comparison of Čech cocycles computed with respect to different covers and different pullbacks, as in the statements about `unitPullback` in the Čech-theoretic development of module presheaves over a scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace
    {Y : Scheme.{u}} [CompactSpace Y] {n : ℕ} (X : Fin n → Scheme.{u}) (h : ∀ j, Y ⟶ X j)
    (𝒰 : ∀ j, (X j).OrderedAffineCover) :
    ∃ (𝒲 : Y.OrderedAffineCover) (lam : ∀ j, 𝒲.ι → (𝒰 j).ι),
      ∀ (j : Fin n) (w : 𝒲.ι), 𝒲.U w ≤ (h j) ⁻¹ᵁ (𝒰 j).U (lam j w) := by sorry
