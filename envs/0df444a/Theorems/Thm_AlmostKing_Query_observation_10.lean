-- Prove2me | Theorems.Thm_AlmostKing_Query_observation_10
-- name    : AlmostKing.Query.observation_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:48.276134+00:00
-- url     : https://prove2.me/theorems/898f2069-2c99-4f8d-b57a-136d4eac7145
-- title:
--   Observation 10 — the coverage inequality
-- statement:
--   For real numbers $\tau,\eta$ satisfying $0\le\tau\le1/2$ and $\eta\ge0$,
--   $$(1-2\tau)(1-\eta)^2\ge1-2\tau-2\eta.$$
--
--   This is the source's numbered arithmetic estimate for converting structural coverage into the desired controlled fraction.
--
--   Differences from the source: none.
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, Observation 10, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib
import Definitions.Def_AlmostKing_Query_Regularity

namespace AlmostKing.Query

/-- Observation 10, p. 8; η has no upper bound. -/
theorem observation_10 (τ η : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 2) (hη : 0 ≤ η) :
    1 - 2 * τ - 2 * η ≤ (1 - 2 * τ) * (1 - η)^2 := by sorry

end AlmostKing.Query
