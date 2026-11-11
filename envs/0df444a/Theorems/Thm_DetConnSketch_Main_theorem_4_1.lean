-- Prove2me | Theorems.Thm_DetConnSketch_Main_theorem_4_1
-- name    : DetConnSketch.Main.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:07.798186+00:00
-- url     : https://prove2.me/theorems/8dbb331a-bb46-4bd1-9586-9e70e417ac70
-- title:
--   Theorem 4.1 — a deterministic one-way connectivity protocol with $\tilde O(n^{7/4})$-bit messages
-- statement:
--   There is a universal constant $C > 0$ such that for every $n \ge 2$ there is a deterministic one-way connectivity protocol on $n$ labeled vertices (correct for every $G_B \le G_A$, with zero error) whose messages have
--   $$m \le C\, n^{7/4} (\log(n+2))^C \ \text{ bits}.$$
--
--   This is the upper clause of Theorem 1.1. Its proof combines Lemma 4.3 (recursion on parent graphs) with Lemma 4.2 (one-sided sketches).
--
--   Differences from the source:
--   - reading: m = Õ(n^{7/4}) bits → ∃ C > 0, ∀ n ≥ 2, a protocol with m ≤ C · n^{7/4} · (log(n+2))^C (one universal C; natural log); reason: equivalent explicit Õ bound; log(n+2) > 1 for n ≥ 2 lets one C absorb the coefficient, exponent and finitely many small n. With unshifted log n, increasing that same C can shrink the bound at n = 2
--   - reading: a message of ≤ m bits (§2.1) → messages exactly in {0,1}^m (Fin m → Bool), as on p. 1; reason: a protocol with messages of at most m bits pads to m + 1 bits, so the bounds are unaffected
--   - encoding: graphs on n labeled vertices; G_A − G_B; 'connected' → SimpleGraph (Fin n); GA \ GB; Mathlib's Connected (which includes Nonempty); reason: same objects for n ≥ 1
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 20 (PDF 24), Theorem 4.1

import Mathlib
import Definitions.Def_DetConnSketch_Main_Protocol

namespace DetConnSketch.Main

/-- Theorem 4.1 (`Õ(n^{7/4})` with one universal constant `C`): for every `n ≥ 2` there is a
deterministic one-way connectivity protocol on `Fin n` whose messages have
`m ≤ C n^{7/4} (log (n+2))^C` bits. -/
theorem theorem_4_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∃ m : ℕ,
      (m : ℝ) ≤ C * (n : ℝ) ^ ((7 : ℝ) / 4) * Real.log ((n : ℝ) + 2) ^ C ∧
      Nonempty (ConnProtocol (Fin n) m) := by sorry

end DetConnSketch.Main
