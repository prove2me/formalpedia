-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_proposition_4_8
-- name    : ExactLearningSeparation678.Randomized.Supplement.proposition_4_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T20:28:38.488054+00:00
-- url     : https://prove2.me/theorems/43dfe331-527b-439f-b372-af1bb3333937
-- title:
--   Proposition 4.8 — $\mathrm{fETD}(C)\le\mathrm{ETD}(C)$
-- statement:
--   For every concept class $C\subseteq\{0,1\}^N$,
--   $$\mathrm{fETD}(C)\le\mathrm{ETD}(C),$$
--   where $\mathrm{ETD}$ is the extended teaching dimension and $\mathrm{fETD}$ the fractional extended teaching dimension of Definition 4.7, both maximized over every $h\in\{0,1\}^N$.
--
--   This is the second clause of Theorem 4.10.
--
--   **Formalization Note** $\mathrm{ETD}$ is a natural number and is compared after casting to the reals. For $C=\emptyset$ the fractional value is read as $0$.
--
--   Differences from the source:
--   - encoding: coordinates [N] of C ⊆ {0,1}^N → an arbitrary finite type ι : Type with decidable equality, concepts ι → Bool; reason: a relabeling of [N]; every N, including N = 0, is an instance
--   - encoding: fETD(C,h) minimizes over c* ∈ C and all real nonnegative coordinate weights, then fETD(C) maximizes over every ambient h → fetdAt is the real infimum of the same total-weight objective over feasible pairs (c*, w); fetd is the supremum over all ambient Boolean functions; reason: for C nonempty feasible weights exist and can be clipped to [0,1] without violating any constraint or increasing cost; finitely many c* and compact weight cubes give attainment, and the outer index is finite and nonempty
--   - reading: fETD(∅), where no exempt concept c* exists and the source assigns no value → 0 (empty infimum); reason: only the empty class is affected; there both sides are 0
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Proposition 4.8, p.32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Proposition 4.8, p.32: `fETD(C) ≤ ETD(C)` for every concept class. -/
theorem proposition_4_8 (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)) :
    fetd C ≤ (etd C : ℝ) := by sorry

end ExactLearningSeparation678.Randomized.Supplement
