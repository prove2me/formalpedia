-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Fractional_ab_nonneg
-- name    : DoubleGreedyUSM.Fractional.ab_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:05:12.640982+00:00
-- url     : https://prove2.me/theorems/cd6ce5e5-40f1-4917-a88e-59fb2117d47a
-- title:
--   Lemma II.1, fractional form (as used in the proof of Lemma A.2) — $a_i + b_i \ge 0$ for Algorithm 4
-- statement:
--   Let $f : 2^{\mathcal N} \to \mathbb R$ be submodular, i.e. $f(A) + f(B) \ge f(A \cup B) + f(A \cap B)$ for all $A, B \subseteq \mathcal N$, and let $F$ be its multilinear extension. Run Algorithm 4 (MultilinearUSM) on $f$ in an order $u_1, \dots, u_n$ of the ground set, producing the vectors $x_i, y_i$. For the quantities
--   $$a_i = F(x_{i-1} + \{u_i\}) - F(x_{i-1}), \qquad b_i = F(y_{i-1} - \{u_i\}) - F(y_{i-1})$$
--   computed by the algorithm at iteration $i$, one has, for every $1 \le i \le n$,
--   $$a_i + b_i \ge 0 .$$
--
--   This is the first step of the proof of Lemma A.2: it guarantees that $a_i$ and $b_i$ cannot both be negative, so the fractions of Algorithm 4 are well defined and the case analysis of Lemma A.2 is exhaustive.
--
--   **Formalization Note.** The paper justifies this by "By Lemma II.1", which is printed for the sets of the deterministic double greedy; the statement here is the fractional inequality actually used, for the vectors of Algorithm 4. Nonnegativity of $f$ is not needed and is not assumed. The order is a duplicate-free list containing every element; $u_i$ is the list entry at index $i - 1$.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, proof of Lemma A.2, first sentence (PDF p. 9), citing Lemma II.1 (PDF p. 3)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Proof of Lemma A.2, first sentence (PDF p. 9), citing Lemma II.1: for Algorithm 4 run on a
submodular `f` in the order `l = [u_1, …, u_n]` of the ground set, `a_i + b_i ≥ 0` at every
iteration `1 ≤ i ≤ n`, where `a_i = F(x_{i−1} + {u_i}) − F(x_{i−1})` and
`b_i = F(y_{i−1} − {u_i}) − F(y_{i−1})`. -/
theorem ab_nonneg {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length) :
    0 ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
      + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega)) := by sorry

end DoubleGreedyUSM.Fractional
