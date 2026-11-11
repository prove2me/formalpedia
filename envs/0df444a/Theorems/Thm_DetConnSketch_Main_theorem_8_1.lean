-- Prove2me | Theorems.Thm_DetConnSketch_Main_theorem_8_1
-- name    : DetConnSketch.Main.theorem_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:07.952128+00:00
-- url     : https://prove2.me/theorems/5d834244-7346-42b9-9e85-37f166fbf9be
-- title:
--   Theorem 8.1 — $\chi(P_n)\ge 2^{\Omega(n^{3/2}/\log n)}$ for all $n\ge n_0$
-- statement:
--   There are constants $c > 0$ and $n_0$ such that for every integer $n \ge n_0$ the universal graph $P_n$ satisfies
--   $$\chi(P_n) \ge 2^{\,c\, n^{3/2}/\log n}. \tag{2}$$
--
--   With Claims 2.2 and 2.5 it gives the lower clause of Theorem 1.1.
--
--   Differences from the source:
--   - reading: 2^{Ω(n^{3/2}/log n)} for n ≥ n0 → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀: 2^{c · n^{3/2} / log n} ≤ χ (natural log); reason: Ω(·) is an existential universal constant fixed before n; the log base is absorbed by c
--   - encoding: χ(P_n) ≥ X → every χ with (universalGraph (Fin n)).Colorable χ has X ≤ χ; reason: χ(P_n) is the least such χ
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 48 (PDF 52), Theorem 8.1

import Mathlib
import Definitions.Def_DetConnSketch_Main_UniversalGraph

namespace DetConnSketch.Main

/-- Theorem 8.1 (`Ω(·)` as an explicit constant `c > 0`): there are `c > 0` and `n₀` such that
for every `n ≥ n₀`, `χ(P_n) ≥ 2^{c n^{3/2} / log n}`: every proper colouring of the universal
graph `P_n` uses at least `2^{c n^{3/2} / log n}` colours. -/
theorem theorem_8_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ χ : ℕ,
      (universalGraph (Fin n)).Colorable χ →
        (2 : ℝ) ^ (c * (n : ℝ) ^ ((3 : ℝ) / 2) / Real.log n) ≤ χ := by sorry

end DetConnSketch.Main
