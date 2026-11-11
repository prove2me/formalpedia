-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_theorem_6_3
-- name    : ApprovalCore.HarmonicEntropy.theorem_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:42:48.692078+00:00
-- url     : https://prove2.me/theorems/c1f8419c-0b6b-4132-9189-f1582d34fbf3
-- title:
--   Theorem 6.3 — from a committee of size at least $k+1$ some deletion lowers $V$ by at most $n/|W|$
-- statement:
--   Throughout, the standing assumption of p. 4 is in force: $\frac{n}{k+1} < q \le \frac{n}{k}$.
--   Let $W \subseteq C$ be a committee of size $|W| \ge k + 1$. Then there exists a candidate $d \in W$ such that
--   $$V(W \setminus \{d\}) \ \ge\ V(W) - \frac{n}{|W|} .$$
--   Together with Theorem 6.2 this gives the swap argument: after adding a candidate to a size-$k$ committee, some candidate can be removed at a cost of at most $\frac{n}{k+1} < q$.
--
--   Differences from the source:
--
--   - encoding: N = [n], C = {c_1, …, c_m}, k ∈ [m − 1], approval sets A_i ⊆ C → Instance n m: voters Fin n, candidates Fin m, A : Fin n → Finset (Fin m), 1 ≤ k and k + 1 ≤ m; reason: same instances; k ∈ [m − 1] is 1 ≤ k ≤ m − 1, i.e. 1 ≤ k and k + 1 ≤ m
--   - encoding: V(W) = max over P124(W) of ∑_i F(r_i, p_i) → V = sSup of the image of P124(W) under ∑_i F(r_i, p_i); reason: the supremum is the paper's maximum once it is attained, which is the milestone section_6_attainment (IsGreatest)
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 12 (PDF 13), Theorem 6.3; proof pp. 13–14

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_Election
import Definitions.Def_ApprovalCore_HarmonicEntropy_Rule

namespace ApprovalCore.HarmonicEntropy

/-- Theorem 6.3 (p. 12): if `|W| ≥ k + 1` then some `d ∈ W` has
`V(W \ {d}) ≥ V(W) − n/|W|`. -/
theorem theorem_6_3 {n m : ℕ} (I : Instance n m) (q : ℝ)
    (hq₁ : (n : ℝ) / ((I.k : ℝ) + 1) < q) (hq₂ : q ≤ (n : ℝ) / (I.k : ℝ))
    (W : Finset (Fin m)) (hW : I.k + 1 ≤ W.card) :
    ∃ d ∈ W, V I.A q (W.erase d) ≥ V I.A q W - (n : ℝ) / (W.card : ℝ) := by sorry

end ApprovalCore.HarmonicEntropy
