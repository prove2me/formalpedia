-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_load_second_moment
-- name    : BarelyTestable.LowerBound.load_second_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:23:01.392243+00:00
-- url     : https://prove2.me/theorems/d37de652-5418-4072-830b-c4b28144aa6c
-- title:
--   Lemma 3.8 — conditional squared-load expectation
-- statement:
--   Let $m\ge5$. Fix any $Y\subseteq B$ and the entire label map $\phi_B$. Sample the entire map $\phi_A$ independently and uniformly. Then
--
--   $$\mathbb E_{\phi_A}\left[\sum_{U\subseteq A}L_Y(U)^2\right]\le250m^{4m}2^{m^2-4m}.$$
--
--   The estimate is uniform in the fixed data and averages only over $\phi_A$. No repair or noise table is an input to the loads.
--
--   Differences from the source:
--   - encoding: expectation over the independently uniform map φ_A → uniformMean on the full finite type LabelMap m; reason: the uniform map law is exactly the product law of all entries; m ≥ 5 makes m²−4m nonnegative
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Lemma 3.8, p. 15 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Lemma 3.8, p.15: the entire B map and Y are fixed before averaging over A. -/
theorem load_second_moment {m : ℕ} (hm : 5 ≤ m) (Y : HalfSet m) (φB : LabelMap m) :
    uniformMean (fun φA : LabelMap m => ∑ U : HalfSet m, (loadY φA φB Y U : ℝ)^2) ≤
      250 * (m : ℝ)^(4*m) * 2^(m^2-4*m) := by sorry

end BarelyTestable.LowerBound
