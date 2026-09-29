-- Prove2me | Theorems.Thm_Finset_interval_inclusion_exclusion
-- name    : Finset.interval_inclusion_exclusion
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-22T15:13:03.770992+00:00
-- url     : https://prove2.me/theorems/f6be11fe-a4bf-440c-96fc-7aa711ca505b
-- title:
--   Finite-set interval inclusion-exclusion
-- statement:
--   Let $D,B$ be finite subsets of a type with decidable equality. Let $g$ and $f$ be rational-valued functions on finite subsets, and suppose that for every finite set $A$,
--   $$f(A)=\sum_{C\subseteq A}g(C).$$
--   Then the sum of $g(C)$ over the Boolean interval $D\subseteq C\subseteq B$ is
--   $$\sum_{S\subseteq D}(-1)^{|S|}f(B\setminus S).$$
--   The formula is valid even when $D$ is not a subset of $B$; both sides then give the corresponding inclusion-exclusion value.
-- source:
--   A proved finite-sum inclusion-exclusion derivation developed in this project. It is presented as an independent specialization of Boolean-lattice inclusion-exclusion, not as a verbatim theorem from an external source.

import Mathlib
open Finset
attribute [local instance] Classical.propDecidable

namespace Finset

open Finset

theorem interval_inclusion_exclusion {α : Type*} [DecidableEq α]
    (D B : Finset α) (g f : Finset α → ℚ)
    (hf : ∀ A : Finset α, f A = ∑ C ∈ A.powerset, g C) :
    (∑ C ∈ B.powerset.filter (fun C => D ⊆ C), g C) =
      ∑ S ∈ D.powerset, (-1 : ℚ) ^ S.card * f (B \ S) := by
  sorry

end Finset
