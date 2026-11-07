-- Prove2me | Theorems.Thm_DSICHardRev_matroid_rank_hierarchy
-- name    : DSICHardRev.matroid_rank_hierarchy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:44.15284+00:00
-- url     : https://prove2.me/theorems/88038e16-edef-41a3-90d6-78b85a303b1a
-- title:
--   §2.3 display, p.10 — Matroid Rank ⊊ Weighted Matroid Rank ⊊ Gross Substitutes
-- statement:
--   For every finite set of items $\iota$:
--
--   1. every matroid rank function is a weighted matroid rank valuation;
--   2. every weighted matroid rank valuation is gross substitutes;
--
--   and if $\iota$ is nonempty, both inclusions are strict:
--
--   3. some weighted matroid rank valuation is not a matroid rank function;
--   4. some monotone, non-negative gross-substitutes valuation is not weighted matroid rank.
--
--   That is,
--   $$\text{Matroid Rank}\subsetneq\text{Weighted Matroid Rank}\subsetneq\text{Gross Substitutes}.$$
--
--   The paper builds its GS hard instances from these subclasses of GS.
--
--   **Formalization Note** Matroids are Mathlib matroids with ground set all of $\iota$; GS is the Kelso–Crawford condition at all real price vectors. A GS valuation is taken monotone and non-negative, as the paper's valuations are (p.9).
--
--   Differences from the source:
--   - reading: GS valuations (not defined in the paper) → Kelso–Crawford gross substitutes at all real price vectors (published GrossSubstitutesOn v Set.univ); reason: the standard definition; requiring all real prices is the more restrictive class
--   - encoding: classes of valuations on M = [m] (m ≥ 1 for the strict inclusions) → for every finite item type ι, nonempty for the strict inclusions; reason: on the empty item set the three classes coincide; otherwise the same statement up to relabelling
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.3, p.10, display "Matroid Rank ⊊ Weighted Matroid Rank ⊊ Gross Substitutes" (Definitions 2.13–2.15)

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model
import Definitions.Def_DSICHardRev_ValuationClasses

namespace DSICHardRev

/-- **§2.3 display, p.10** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design,
Revisited*, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…)):
`Matroid Rank ⊊ Weighted Matroid Rank ⊊ Gross Substitutes`.

**Formalization Note.** The display is stated in full, for every nonempty finite item set `ι`:
(1) every matroid rank function (Definition 2.14) is weighted matroid rank (Definition 2.15);
(2) every weighted matroid rank valuation is gross substitutes (Kelso–Crawford at all real price
vectors); (3) some weighted matroid rank valuation is not a matroid rank function; (4) some
(monotone, non-negative) gross-substitutes valuation is not weighted matroid rank. The inclusions
(1)–(2) hold for every finite `ι`; strictness needs `ι` nonempty (on the empty item set the three
classes coincide). -/
theorem matroid_rank_hierarchy :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : Finset ι → ℝ),
        IsMatroidRankFn r → IsWeightedMatroidRank r) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : Finset ι → ℝ),
        IsWeightedMatroidRank v → KelsoCrawford.OneSided.GrossSubstitutesOn v Set.univ) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι],
        ∃ v : Finset ι → ℝ, IsWeightedMatroidRank v ∧ ¬ IsMatroidRankFn v) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι],
        ∃ v : Finset ι → ℝ, Monotone v ∧ (∀ S, 0 ≤ v S) ∧
          KelsoCrawford.OneSided.GrossSubstitutesOn v Set.univ ∧ ¬ IsWeightedMatroidRank v) := by sorry

end DSICHardRev
