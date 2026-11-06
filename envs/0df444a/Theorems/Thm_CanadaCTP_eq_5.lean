-- Prove2me | Theorems.Thm_CanadaCTP_eq_5
-- name    : CanadaCTP.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:18:07.217173+00:00
-- url     : https://prove2.me/theorems/f44c0d7e-c92e-49a4-93e4-227112f807d7
-- title:
--   Eq. (5) — $1-e^{-s}\ge(1-e^{-1})\min\{1,s\}$
-- statement:
--   For every $s\ge0$,
--   $$
--   1-e^{-s}\ \ge\ (1-e^{-1})\min\{1,s\}.
--   $$
--
--   It converts the product of failure probabilities of the $k$ paths into a sum in the proof of Lemma 10 (the correlation-gap step).
--
--   Differences from the source: none.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Eq. (5), p.18

import Mathlib

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Eq. (5), p.18: for all `s ≥ 0`, `1 − e^{−s} ≥ (1 − e^{−1})·min{1, s}`. -/
theorem eq_5 (s : ℝ) (hs : 0 ≤ s) :
    (1 - Real.exp (-1)) * min 1 s ≤ 1 - Real.exp (-s) := by sorry

end CanadaCTP
