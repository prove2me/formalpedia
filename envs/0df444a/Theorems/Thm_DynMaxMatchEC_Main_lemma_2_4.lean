-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_lemma_2_4
-- name    : DynMaxMatchEC.Main.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:02:21.387713+00:00
-- url     : https://prove2.me/theorems/13075d5b-dee3-4c37-9dbc-3dc879a56a94
-- title:
--   Lemma 2.4 — AlgGreedy keeps the element-hitting game's value at most 3h log n / r
-- statement:
--   In the element-hitting game with $n\ge1$ elements and integral parameters $h,r\ge1$, in which the resetting player is AlgGreedy (reset $r$ elements with the largest positive counters), every counter at the end of every iteration satisfies
--   $$N_j\le\frac{3h\log_2 n}{r},$$
--   however the loading player plays and however AlgGreedy breaks ties. The game is the derandomization tool behind Theorem 2.5: it replaces random resetting of hit elements.
--
--   Differences from the source:
--   - encoding: regardless of how the loading player plays → for every counter vector reachable by some sequence of valid loading moves and some tie-breaking of AlgGreedy; reason: every adaptive play is such a sequence and every sequence is played by an oblivious loading player
--   - encoding: elements e₁, …, eₙ; a set Hᵢ with hit amounts Δⱼ ≥ 1 → Fin n; a hit vector whose support is Hᵢ; reason: Lean convention
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 13, Lemma 2.4

import Mathlib
import Definitions.Def_DynMaxMatchEC_Main_HittingGame

namespace DynMaxMatchEC.Main

/-- **Lemma 2.4** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 13). In the
element-hitting game on `n ≥ 1` elements with integral parameters `h, r ≥ 1`, when the resetting
player is AlgGreedy, every counter at the end of every iteration is at most `3h·log₂ n / r`, for every
play of the loading player and every tie-breaking of AlgGreedy. -/
theorem lemma_2_4 (n h r : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hr : 1 ≤ r) (N : Fin n → ℕ)
    (hN : Reachable h r N) (j : Fin n) :
    (N j : ℝ) ≤ 3 * h * Real.logb 2 n / r := by sorry

end DynMaxMatchEC.Main
