-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_theorem_3_2
-- name    : ApprovalCore.HarmonicEntropy.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:24.508208+00:00
-- url     : https://prove2.me/theorems/e252e30f-dbaf-4c7d-9f78-16ed6c19947b
-- title:
--   Theorem 3.2 — $W \in \mathcal W$ satisfies core+ iff $P_{1234}(W) \ne \emptyset$
-- statement:
--   Let $(A, k)$ be an approval-based committee election and $q > 0$ a quota. A committee $W$ with $|W| \le k$ satisfies core+ at quota $q$ if and only if there exists a payment system $(r, p)$ for $W$ satisfying (P1)–(P4):
--   $$W \text{ satisfies core+} \iff P_{1234}(W) \ne \emptyset .$$
--   This characterizes core+ through payment systems; the direction ($\Leftarrow$) is the one used to show that the harmonic entropy rule satisfies core+, and ($\Rightarrow$) is a Farkas-lemma argument.
--
--   Differences from the source:
--
--   - generalization: quota in the standing range n/(k+1) < q ≤ n/k (p. 4) → any quota q > 0; reason: the proof (Appendix A.1) uses only q > 0 (the quota of p. 4 is positive by definition); the standing range implies q > 0, so the Lean statement specializes to the paper's
--   - encoding: N = [n], C = {c_1, …, c_m}, k ∈ [m − 1], approval sets A_i ⊆ C → Instance n m: voters Fin n, candidates Fin m, A : Fin n → Finset (Fin m), 1 ≤ k and k + 1 ≤ m; reason: same instances; k ∈ [m − 1] is 1 ≤ k ≤ m − 1, i.e. 1 ≤ k and k + 1 ≤ m
--   - encoding: payments p_ic only for approved winners c ∈ A_i ∩ W → p : Fin n → Fin m → ℝ with p i c = 0 for c ∉ A_i ∩ W, imposed by IsPaymentSystem in every P-set; reason: the forced zeros never enter (P1), (P2), (P4) or a voter's distribution, so the payment systems are the paper's
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 5 (PDF 6), Theorem 3.2; proof pp. 23–25 (PDF 24–26), Appendix A.1

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_Election

namespace ApprovalCore.HarmonicEntropy

/-- Theorem 3.2 (p. 5): a committee `W ∈ W` satisfies core+ at quota `q` if and only if
`P1234(W)` is non-empty; stated for every quota `q > 0`. -/
theorem theorem_3_2 {n m : ℕ} (I : Instance n m) (q : ℝ) (hq : 0 < q)
    (W : Finset (Fin m)) (hW : W.card ≤ I.k) :
    SatisfiesCorePlus I q W ↔ (P1234 I.A q W).Nonempty := by sorry

end ApprovalCore.HarmonicEntropy
