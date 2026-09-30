-- Prove2me | Theorems.Thm_ComputationalLearning_decision_lists_pac_learnable
-- name    : ComputationalLearning.decision_lists_pac_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:04:50.031978+00:00
-- url     : https://prove2.me/theorems/688cae9c-fafb-4d73-827e-f332c354e915
-- title:
--   Theorem 2.3: k-decision lists are PAC learnable by the greedy decision-list algorithm, which never fails and whose outputs are consistent
-- statement:
--   **Theorem 2.3.** For any fixed $k \ge 1$, the representation class of $k$-decision lists is efficiently PAC learnable.
--
--   Formally, for the greedy decision-list algorithm of p. 44 (repeatedly append a useful condition with its label and remove the examples it satisfies, until none is left), with conditions the conjunctions of $k$ literals ($M = (2n)^k$ of them): (i) on every sample labeled by a $k$-decision list, every partial run with examples remaining can be extended by a useful condition (the algorithm always succeeds); (ii) every complete output is consistent with its sample; (iii) for every target $k$-decision list, distribution $D$ on $\{0,1\}^n$, $0 < \epsilon \le 1$, $0 < \delta < 1$ and $m \ge (1/\epsilon)(\ln N + \ln(1/\delta))$ with $N = 2(2M+1)^M$, the probability that some output of the algorithm has error greater than $\epsilon$ is at most $\delta$ (an output uses each condition at most once, so the hypothesis class has at most $N$ members and Theorem 2.2 applies); (iv) $k$-decision lists are PAC learnable using $k$-decision lists. The book proves $k = 1$ and reduces general $k$ to it by expansion; here the conditions are the $k$-conjunctions directly, so the hypothesis is a $k$-decision list.
--
--   **`n ≥ 1`.** The conditions are conjunctions of exactly $k$ literals, fewer by repetition, so for $k \ge 1$ there is no empty (always true) condition. When no condition of the target is satisfied by a remaining example, every remaining example carries the target's default bit, and then any condition satisfied by a remaining example is useful; such a condition exists as soon as there is a variable. With $n = 0$ and $k \ge 1$ there are no conditions at all, and the greedy algorithm would fail on every nonempty sample, so the statement takes the book's $n \ge 1$ (variables $x_1, \dots, x_n$). The book's own proof, "the first condition $z$ in the target decision list such that $S_z$ is non-empty is a useful literal", has the same gap when every remaining example falls through to the default; the argument above closes it.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §2.4 pp. 42-44, Theorem 2.3 with its proof (the greedy algorithm, useful literals, the O(n log n)-bit encoding)

import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory

namespace ComputationalLearning

/-- **Theorem 2.3** (p. 43). For any fixed `k ≥ 1`, the representation class of `k`-decision lists
over `n ≥ 1` variables is (efficiently) PAC learnable, by the greedy decision-list algorithm: on a sample labeled by a
`k`-decision list the algorithm always finds a useful condition while examples remain (so it
never fails), every output is consistent with the sample, and with
`m ≥ (1/ε)(ln N + ln(1/δ))` examples, `N = 2(2M + 1)^M` for `M = (2n)^k` the number of
conditions (an output uses each condition at most once, so it is one of at most `N` lists), the
probability that some output has error greater than `ε` is at most `δ`; hence `k`-decision
lists are PAC learnable using `k`-decision lists. -/
theorem decision_lists_pac_learnable {n k : ℕ} (hn : 0 < n) (L₀ : DecisionList n k)
    (D : Measure (Cube (Fin n))) [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 1 / ε * (Real.log (2 * (2 * (Fintype.card (Condition n k) : ℝ) + 1) ^
      Fintype.card (Condition n k)) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalDL L₀) S →
      ∀ (steps : List (Condition n k × Bool)) (R : Finset (Fin m)),
        IsGreedyPrefix S steps R → R.Nonempty → ∃ (c : Condition n k) (b : Bool), IsUseful S R c b) ∧
    (∀ (S : Fin m → Cube (Fin n) × Bool) (L : DecisionList n k),
      IsGreedyOutput S L → IsConsistent (evalDL L) S) ∧
    sampleLaw D (evalDL L₀) m
      {S | ∃ L : DecisionList n k, IsGreedyOutput S L ∧ ε < errorOf D (evalDL L₀) (evalDL L)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (decisionListClass n k) (decisionListClass n k) := by sorry

end ComputationalLearning
