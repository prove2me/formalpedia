-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_finset_finrank_comp_eq_sum_toNat_length_stalk_quotient_ker_stalkMap
-- name    : AlgebraicGeometry.IsClosedImmersion.exists_finset_finrank_comp_eq_sum_toNat_length_stalk_quotient_ker_stalkMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/3ee32fdc-1b10-5c2f-9166-1c7c292f9247
-- title:
--   Degree of a finite closed subscheme as a sum of stalk lengths
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ and $K$ be schemes, let $f : A \to \operatorname{Spec} k$ be a morphism, and let $\kappa : K \to A$ be a closed immersion such that the composite $\kappa \gg f : K \to \operatorname{Spec} k$ is a finite morphism. The assertion is that there exists a finite set $T$ of points of $K$ such that: (i) every point of $K$ belongs to $T$ (so the underlying space of $K$ is finite); (ii) for every point $y'$ of $K$ the singleton $\{\kappa(y')\}$ is closed in $A$; and (iii) the integer obtained from the natural number $\operatorname{finrank}$ of $\kappa \gg f$ at the closed point of $\operatorname{Spec} k$ — that is, the $k$-rank of the fibre of $(\kappa \gg f)_*\mathcal O_K$ there — equals $$\sum_{y' \in T} \Bigl(\operatorname{length}_{\mathcal O_{A,\kappa(y')}}\bigl(\mathcal O_{A,\kappa(y')}/\ker(\kappa^{\sharp}_{y'})\bigr)\Bigr)\!,$$ each summand being the $\mathbb N_\infty$-valued module length pushed to $\mathbb N$ by `ENat.toNat` and then to $\mathbb Z$, where $\kappa^{\sharp}_{y'} : \mathcal O_{A,\kappa(y')} \to \mathcal O_{K,y'}$ is the induced map on stalks. Here $k$ and the two schemes live in the bottom universe.
--
--   This is the standard count of the degree over an algebraically closed field of a finite closed subscheme of a scheme, localised at the points of the subscheme: the degree is the sum of the lengths of the quotients of the local rings of the ambient scheme by the kernels of the stalk maps. It is used in the computation of the Euler characteristic of a Mumford bundle twisted by a pullback in [`AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer`](thm.html#AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_finset_finrank_comp_eq_sum_toNat_length_stalk_quotient_ker_stalkMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.exists_finset_finrank_comp_eq_sum_toNat_length_stalk_quotient_ker_stalkMap
    (k : Type) [Field k] [IsAlgClosed k] {A K : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (κ : K ⟶ A) [IsClosedImmersion κ] [IsFinite (κ ≫ f)] :
    ∃ T : Finset K, (∀ y' : K, y' ∈ T) ∧ (∀ y' : K, IsClosed ({κ.base y'} : Set A)) ∧
      (((κ ≫ f).finrank (IsLocalRing.closedPoint k) : ℕ) : ℤ) =
        ∑ y' ∈ T, ((Module.length (A.presheaf.stalk (κ.base y'))
          ((A.presheaf.stalk (κ.base y')) ⧸ RingHom.ker (κ.stalkMap y').hom)).toNat : ℤ) := by sorry
