-- Prove2me | Theorems.Thm_BddExp3SUM_theorem_1
-- name    : BddExp3SUM.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:55.921161+00:00
-- url     : https://prove2.me/theorems/bcda85d8-594d-42f0-aa39-a20c6b946c40
-- title:
--   Theorem 1: for each $M\ge2$, one randomized word-RAM program solves three-list 3SUM over $\prod_j\mathbb Z_{m_j}$, $m_j\mid M$, in worst-case time $O_{M,c}(n^{2-\delta_M}\,\mathrm{polylog}\,n)$
-- statement:
--   Fix an integer $M\ge2$, and put
--
--   $$C=\lceil\log_2M\rceil,\quad\eta=\min\{1/18,1/(8C)\},\quad\gamma=63/1000,\quad\delta_M=\eta\gamma/2.$$
--
--   There are a single program $P$ of the word RAM and an exponent $A$ such that, for every $c>0$, there are $b$ and $K$ with the following property. For every $n$, every instance with moduli $m_1,\dots,m_r$ dividing $M$, $\prod_jm_j\le n^c$, and lists of size at most $n$, and every word width $W\ge b(\lfloor\log_2(n+r)\rfloor+1)$:
--
--   1. on every coin tape the program halts within $K\bigl((n+2)^{2-\delta_M}\log(n+2)^A+r\bigr)$ steps, and if it accepts, the three output cells hold indices of a zero-sum triple;
--   2. if a zero-sum triple exists, the program accepts with probability at least $3/4$ over independent fair coins.
--
--   So the algorithm always rejects negative inputs and returns only verified witnesses. The saving $\delta_M$ does not depend on $c$. It extends truly subquadratic 3SUM from exponent dividing $p^2$ to every bounded exponent.
--
--   Differences from the source:
--   - reading: "Trivial factors are discarded", with time O_{M,c}(n^{2−δ_M} polylog n) and words of O_{M,c}(log n) bits → moduli m_j = 1 are allowed, with an additive r in the time and n + r in the word-width threshold; reason: raw r is not bounded by n when moduli equal 1, and discarding them requires reading r moduli; with no trivial factor, r ≤ c log₂ n and the bound and the word size are the printed ones
--   - reading: "a uniform classical randomized algorithm which, for every fixed c > 0, ..." in O_{M,c}(n^{2−δ_M} polylog n) → ∃ P, A before c, then ∃ b, K after c; reason: the stronger reading; the algorithm’s parameters never use c, and only the constant and word factor depend on it
--   - reading: a "uniform classical randomized algorithm", machine not named; charged words → the published word RAM EndStatement with no division or shift, every word width above the threshold; reason: the machine of the platform’s integer 3SUM; "bit simulation contributes a polynomial logarithmic factor" (p.1)
--   - encoding: random-bit generation → a fair-coin tape preloaded in the negative cells, read by load; reason: one load per coin; the instruction set is unchanged
--   - encoding: n^{2−δ_M} polylog n → (n+2)^{2−δ_M} (log(n+2))^A; reason: keeps the bound positive at n ∈ {0, 1}; the same O(·) for n ≥ 2
--   - encoding: "always rejects negative inputs, returns only verified witnesses" → on every tape, verdict true implies a witness in the output cells; reason: the two claims at once; rejection on negative inputs is a one-line corollary
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), Theorem 1, p.1 (PDF p.2); the input model, §1, p.1

import Mathlib
import Definitions.Def_BddExp3SUM_Instance

open scoped ENNReal

namespace BddExp3SUM

/-- Theorem 1, p.1 (Zeng, Wang, Cao, Dai, Wang, *Truly Subquadratic 3SUM over Every Bounded-Exponent
Abelian Group*, STOC 2027 submission, manuscript sha256 19546c9a…).

**Formalization Note.**
* **Order of quantifiers.** One program `P` and one polylog exponent `A` for each `M`, before `c`; the
  word factor `b` and the constant `K` depend on `M` and `c`.
* **Time.** On **every** coin tape the run halts within `K ((n+2)^{2-δ_M} (log(n+2))^A + r)` steps.
  `n + 2` keeps the bound positive at small `n`. The additive `r` pays for "Trivial factors are discarded"
  (p.1): `r` is unbounded when moduli equal `1`, and on an instance without trivial factors
  `r ≤ c log₂ n`, which the first term absorbs.
* **Words.** Every width `W ≥ b(⌊log₂(n+r)⌋ + 1)`; with no trivial factor this is `O_{M,c}(log n)`.
* **Verdict.** On every tape, accepting implies that the three output cells hold a verified witness.
  So a negative input is rejected on every tape.
* **Success.** Probability at least `3/4` on each positive input. The accepting set depends on finitely many
  coordinates of the tape, since every run halts within the bound, so it is measurable. -/
theorem theorem_1 :
    ∀ M : ℕ, 2 ≤ M → ∃ (P : List EndStatement.Instr) (A : ℕ),
      ∀ c : ℝ, 0 < c → ∃ (b : ℕ) (K : ℝ),
        ∀ (n : ℕ) (x : Instance M), x.order ≤ (n : ℝ) ^ c →
          x.L₁.length ≤ n → x.L₂.length ≤ n → x.L₃.length ≤ n →
          ∀ W : ℕ, b * (Nat.log2 (n + x.r) + 1) ≤ W →
            (∀ tape : ℕ → Bool, ∃ (t : ℕ) (v : Bool) (mem : ℤ → BitVec W),
              (t : ℝ) ≤ K * (((n : ℝ) + 2) ^ (2 - δ M) * Real.log ((n : ℝ) + 2) ^ A + x.r) ∧
              EndStatement.exec P t 0 (x.memory W n tape) = some (v, mem) ∧
              (v = true → x.IsWitness (x.out mem 0) (x.out mem 1) (x.out mem 2))) ∧
            (x.HasWitness → (3 / 4 : ℝ≥0∞) ≤ coinLaw {tape | x.Accepts P W n tape}) := by sorry

end BddExp3SUM
