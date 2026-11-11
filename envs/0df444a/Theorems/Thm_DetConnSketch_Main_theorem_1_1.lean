-- Prove2me | Theorems.Thm_DetConnSketch_Main_theorem_1_1
-- name    : DetConnSketch.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:05.402022+00:00
-- url     : https://prove2.me/theorems/7bca3f88-9ff3-4c2c-8287-c85227eaaf67
-- title:
--   Theorem 1.1 — deterministic one-way connectivity under edge deletions: $\tilde O(n^{1.75})$-bit protocols exist and $\tilde\Omega(n^{1.5})$ bits are necessary
-- statement:
--   Alice holds a graph $G_A$ on $n$ labeled vertices, Bob a graph $G_B \le G_A$; Alice sends one message of $m$ bits depending on $G_A$ only, and Bob must decide with zero error, for every $G_B \le G_A$, whether $G_A - G_B$ is connected. Then:
--
--   **(upper)** there is a universal constant $C > 0$ such that for every $n \ge 2$ some deterministic one-way connectivity protocol on $n$ vertices has
--   $$m \le C\, n^{7/4}(\log(n+2))^C;$$
--
--   **(lower)** there are constants $c > 0$ and $n_0$ such that for every $n \ge n_0$ every deterministic one-way connectivity protocol on $n$ vertices has
--   $$m \ge c\,\frac{n^{3/2}}{\log n}.$$
--
--   Deciding connectivity thus needs polynomially less than the $\Omega(n^2)$ bits of recovering a single surviving edge, and polynomially more than the $\tilde O(n)$ bits of randomized sketches.
--
--   Differences from the source:
--   - reading: m = Õ(n^{7/4}) bits → ∃ C > 0, ∀ n ≥ 2, a protocol with m ≤ C · n^{7/4} · (log(n+2))^C (one universal C; natural log); reason: equivalent explicit Õ bound; log(n+2) > 1 for n ≥ 2 lets one C absorb the coefficient, exponent and finitely many small n. With unshifted log n, increasing that same C can shrink the bound at n = 2
--   - reading: messages of length Ω̃(n^{1.5}) bits → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, every protocol on Fin n with m-bit messages has c · n^{3/2} / log n ≤ m; reason: the form Theorem 8.1 with Claims 2.2 and 2.5 gives; it implies every Ω̃ reading
--   - reading: a message of ≤ m bits (§2.1) → messages exactly in {0,1}^m (Fin m → Bool), as on p. 1; reason: a protocol with messages of at most m bits pads to m + 1 bits, so the bounds are unaffected
--   - encoding: graphs on n labeled vertices; G_A − G_B; 'connected' → SimpleGraph (Fin n); GA \ GB; Mathlib's Connected (which includes Nonempty); reason: same objects for n ≥ 1
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 2 (PDF 6), Theorem 1.1

import Mathlib
import Definitions.Def_DetConnSketch_Main_Protocol

namespace DetConnSketch.Main

/-- Theorem 1.1, both clauses: (upper, `Õ(n^{1.75})`) there is a universal `C` such that for
every `n ≥ 2` some deterministic one-way connectivity protocol on `Fin n` has messages of
`m ≤ C n^{7/4} (log (n+2))^C` bits; (lower, `Ω̃(n^{1.5})`) there are `c > 0` and `n₀` such that for
every `n ≥ n₀` every deterministic one-way connectivity protocol on `Fin n` with `m`-bit
messages has `m ≥ c n^{3/2} / log n`. -/
theorem theorem_1_1 :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∃ m : ℕ,
      (m : ℝ) ≤ C * (n : ℝ) ^ ((7 : ℝ) / 4) * Real.log ((n : ℝ) + 2) ^ C ∧
      Nonempty (ConnProtocol (Fin n) m)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ,
      Nonempty (ConnProtocol (Fin n) m) → c * (n : ℝ) ^ ((3 : ℝ) / 2) / Real.log n ≤ m) := by sorry

end DetConnSketch.Main
