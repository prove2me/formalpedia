-- Prove2me | Theorems.Thm_BddExp3SUM_lemma_7
-- name    : BddExp3SUM.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:14.540806+00:00
-- url     : https://prove2.me/theorems/b02e7e8e-e8bf-42e2-ab3f-2995451a0295
-- title:
--   Lemma 7, last sentence (Alman–Vassilevska Williams): prescribed entries of $XY$ in $O(N^2/D^{0.063}+wD^{0.437})$ time on the word RAM
-- statement:
--   Fix $\kappa$. There are one word-RAM program and constants $b,K$ such that, for all $N\ge D^{18}$, $D\ge1$, all $X\in\mathbb Z^{N\times D}$ and $Y\in\mathbb Z^{D\times N}$ with entries of absolute value at most $N^\kappa$, and all $w$ prescribed positions, the program computes those entries of $XY$ deterministically within
--
--   $$K\bigl(N^2/D^{0.063}+wD^{0.437}\bigr)$$
--
--   steps, at every word width $W\ge b(\lfloor\log_2(N+w)\rfloor+1)$. For $w\le N^2/\sqrt D$ this is $O(N^2/D^{0.063})$.
--
--   This is the only external algorithmic input of the mission. The paper uses it as a cited theorem.
--
--   **Formalization Note** This item poses the sentence the proof of Theorem 1 uses. The preprocess-then-query interface and the space bound of Lemma 7 are not posed.
--
--   Differences from the source:
--   - generalization: at most N²/√D prescribed entries, in O(N²/D^{0.063}) time → every w, in O(N²/D^{0.063} + w D^{0.437}) time, with word width in terms of N + w; reason: for w ≤ N²/√D the second term is at most the first, which is the printed bound
--   - reading: a theorem cited from [AVW26], with no machine named here; only its last sentence → the same claim on the published word RAM EndStatement, one program per κ, every W above the threshold; reason: the goal needs one machine; Theorem 1’s proof uses only this sentence ("one call to Lemma 7 computes all required positions")
--   - encoding: entries of absolute value N^{O(1)} → for every κ, entries with |·| ≤ N^κ; reason: the meaning of O(1) in the exponent
--   - encoding: D a matrix dimension, no condition stated → hypothesis 1 ≤ D; reason: at D = 0 the bound N²/D^{0.063} is undefined (Lean's N²/0 = 0 would demand time 0); it excludes only that undefined case, and the paper's D = p^q ≥ 2
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 7, p.6 (PDF p.7), citing Alman and Vassilevska Williams, arXiv:2610.06783v1, Corollary 26

import Mathlib
import Definitions.Def_BddExp3SUM_ThinProduct

namespace BddExp3SUM

/-- Lemma 7, last sentence, p.6 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256
19546c9a…, citing Alman and Vassilevska Williams, arXiv:2610.06783v1, Corollary 26): "at most
`N²/√D` prescribed entries can be computed in `O(N²/D^{0.063})` time", on the published word RAM.

**Formalization Note.** For every bound `N^κ` on the entries ("`N^{O(1)}`") there is one program, one word
factor `b` and one constant `K`, for all `N`, `X`, `Y` and all `w`, with time `K (N²/D^{0.063} + w
D^{0.437})` and every word width `W ≥ b(⌊log₂(N + w)⌋ + 1)`. For `w ≤ N²/√D` the second term is at most
the first. -/
theorem lemma_7 :
    ∀ κ : ℕ, ∃ (P : List EndStatement.Instr) (b : ℕ) (K : ℝ),
      ∀ (N : ℕ) (x : ThinInstance N), 1 ≤ x.D → x.D ^ 18 ≤ N →
        (∀ i t, (x.X i t).natAbs ≤ N ^ κ) → (∀ t j, (x.Y t j).natAbs ≤ N ^ κ) →
        ∀ W : ℕ, b * (Nat.log2 (N + x.w) + 1) ≤ W →
          ∃ t : ℕ, (t : ℝ) ≤ K * ((N : ℝ) ^ 2 / (x.D : ℝ) ^ ((63 : ℝ) / 1000) +
              x.w * (x.D : ℝ) ^ ((437 : ℝ) / 1000)) ∧
            ThinProduct.SolvedBy (n := N) x P W t := by sorry

end BddExp3SUM
