-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_theorem_6_2
-- name    : ApprovalCore.HarmonicEntropy.theorem_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:42:52.764698+00:00
-- url     : https://prove2.me/theorems/9cff9fe2-8787-4272-9a64-33fdfaaf743b
-- title:
--   Theorem 6.2 — a (P3) violation lets one add a candidate and raise $V$ by at least $q$
-- statement:
--   Throughout, the standing assumption of p. 4 is in force: $\frac{n}{k+1} < q \le \frac{n}{k}$.
--   Let $W \subseteq C$ be a committee and let $(r, p) \in P_{124}(W)$ be an optimal payment system of $W$, i.e. $\sum_i F(r_i, p_i) = V(W)$. If some candidate $c \in C \setminus W$ satisfies $\sum_{i \in N_c} r_i \ge q$, then
--   $$V(W \cup \{c\}) \ \ge\ V(W) + q .$$
--   A violation of (P3) in an optimal payment system thus identifies a candidate whose addition increases the harmonic entropy value by at least the quota; this is the first half of the swap argument.
--
--   Differences from the source:
--
--   - encoding: N = [n], C = {c_1, …, c_m}, k ∈ [m − 1], approval sets A_i ⊆ C → Instance n m: voters Fin n, candidates Fin m, A : Fin n → Finset (Fin m), 1 ≤ k and k + 1 ≤ m; reason: same instances; k ∈ [m − 1] is 1 ≤ k ≤ m − 1, i.e. 1 ≤ k and k + 1 ≤ m
--   - encoding: payments p_ic only for approved winners c ∈ A_i ∩ W → p : Fin n → Fin m → ℝ with p i c = 0 for c ∉ A_i ∩ W, imposed by IsPaymentSystem in every P-set; reason: the forced zeros never enter (P1), (P2), (P4) or a voter's distribution, so the payment systems are the paper's
--   - encoding: V(W) = max over P124(W) of ∑_i F(r_i, p_i) → V = sSup of the image of P124(W) under ∑_i F(r_i, p_i); reason: the supremum is the paper's maximum once it is attained, which is the milestone section_6_attainment (IsGreatest)
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 12 (PDF 13), Theorem 6.2

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_Election
import Definitions.Def_ApprovalCore_HarmonicEntropy_Rule

namespace ApprovalCore.HarmonicEntropy

/-- Theorem 6.2 (p. 12): if `(r, p)` is an optimal payment system of `W` and some
`c ∈ C \ W` has `∑_{i ∈ N_c} r_i ≥ q`, then `V(W ∪ {c}) ≥ V(W) + q`. -/
theorem theorem_6_2 {n m : ℕ} (I : Instance n m) (q : ℝ)
    (hq₁ : (n : ℝ) / ((I.k : ℝ) + 1) < q) (hq₂ : q ≤ (n : ℝ) / (I.k : ℝ))
    (W : Finset (Fin m)) (rp : PaymentPair n m) (hopt : IsOptimal I.A q W rp)
    (c : Fin m) (hc : c ∉ W) (hR : ∑ i ∈ supporters I.A c, rp.1 i ≥ q) :
    V I.A q (insert c W) ≥ V I.A q W + q := by sorry

end ApprovalCore.HarmonicEntropy
