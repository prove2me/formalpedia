-- Prove2me | Theorems.Thm_EffRobustLearn_fact_C_3_item_3
-- name    : EffRobustLearn.fact_C_3_item_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:35:28.136196+00:00
-- url     : https://prove2.me/theorems/6783cb11-f07e-4fb7-a8e5-792c0165fd9e
-- title:
--   Fact C.3 item 3 — Rademacher complexity is invariant under convexification
-- statement:
--   For a distribution $D$, a class $H$ of $[-1,1]$-valued functions and $|S|\ge1$,
--   $$R_{|S|,D}(\mathrm{conv}(H))=R_{|S|,D}(H).$$
--
--   Differences from the source:
--   - encoding: a class in the sense of Definition C.2 → $[-1,1]$-valued real class; the integrands agree at every sample, so no measurability is assumed; reason: the supremum of a linear functional over a hull equals that over the set; the integrals of the same function agree
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Fact C.3 item 3, p.41 (PDF p.42), cited from [MRT18, Lemma 7.4]

import Mathlib
import Definitions.Def_EffRobustLearn_rademacherD

open MeasureTheory

namespace EffRobustLearn

/-- Fact C.3 item 3, p.41 (arXiv:2609.17655, held version, sha256 312a0857…), cited from [MRT18, Lemma 7.4]: `R_{|S|,D}(conv(H)) = R_{|S|,D}(H)`.

**Formalization Note.** Stated for `[-1, 1]`-valued real classes, the domain of Definition C.2. The two integrands agree at every sample, so no measurability
hypothesis is needed. The published `FoundationsML.Boosting.rademacher_complexity_conv_hull` is on the retired clipped definition and is not this statement. -/
theorem fact_C_3_item_3 {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Set (X → ℝ)) (hH : ∀ f ∈ H, ∀ x, |f x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    rademacherD D n (convexHull ℝ H) = rademacherD D n H := by sorry

end EffRobustLearn
