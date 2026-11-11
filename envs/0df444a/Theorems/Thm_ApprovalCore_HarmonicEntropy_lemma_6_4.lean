-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_lemma_6_4
-- name    : ApprovalCore.HarmonicEntropy.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:42:51.268446+00:00
-- url     : https://prove2.me/theorems/9b1c8876-c25b-466a-aee5-2f53e111891d
-- title:
--   Lemma 6.4 — an optimal system with a de-reserved system whose unsaturated candidates carry the largest payment and lower $F$ by it
-- statement:
--   Throughout, the standing assumption of p. 4 is in force: $\frac{n}{k+1} < q \le \frac{n}{k}$.
--   For every committee $W \subseteq C$ there exist an optimal payment system $(r, p) \in P_{124}(W)$ and a de-reserved system $(\hat r, \hat p)$ derived from it such that, for every candidate $d \in W$ that is unsaturated in $(\hat r, \hat p)$ (i.e. $\sum_{i \in N_d} \hat p_{id} < q$) and every voter $i \in N_d$:
--
--   (a) $\hat p_{id} \ge \hat p_{ic}$ for every $c \in A_i \cap W$, and
--
--   (b) $F(\hat r_i, \hat p_i) = F(r_i, p_i) - \hat p_{id}$.
--
--   This is the technical step behind Theorem 6.3: after redistributing reserves, deleting an unsaturated candidate costs each of its supporters exactly her payment to it.
--
--   Differences from the source:
--
--   - encoding: N = [n], C = {c_1, …, c_m}, k ∈ [m − 1], approval sets A_i ⊆ C → Instance n m: voters Fin n, candidates Fin m, A : Fin n → Finset (Fin m), 1 ≤ k and k + 1 ≤ m; reason: same instances; k ∈ [m − 1] is 1 ≤ k ≤ m − 1, i.e. 1 ≤ k and k + 1 ≤ m
--   - encoding: payments p_ic only for approved winners c ∈ A_i ∩ W → p : Fin n → Fin m → ℝ with p i c = 0 for c ∉ A_i ∩ W, imposed by IsPaymentSystem in every P-set; reason: the forced zeros never enter (P1), (P2), (P4) or a voter's distribution, so the payment systems are the paper's
--   - encoding: V(W) = max over P124(W) of ∑_i F(r_i, p_i) → V = sSup of the image of P124(W) under ∑_i F(r_i, p_i); reason: the supremum is the paper's maximum once it is attained, which is the milestone section_6_attainment (IsGreatest)
--   - encoding: voter i's vector (r_i, p_i) with p_i = (p_ic)_{c ∈ A_i ∩ W} → voterDist: Fin (|A_i ∩ W| + 1) → ℝ, reserve at index 0, then payments in increasing candidate index; reason: the paper fixes no order of the coordinates; this is the order of its notation (r_i, p_i) with C = {c_1, …, c_m}, and F is symmetric (Proposition 5.2)
--   - reading: 'for every unsaturated candidate d ∈ W' (the payment system is not named) → d unsaturated in the de-reserved system (r̂, p̂); reason: the proof (p. 14) and the use in Theorem 6.3 (p. 13) take d unsaturated in (r̂, p̂); only then does the de-reserved property give r̂_i = 0, which (b) needs
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 13 (PDF 14), Lemma 6.4 (de-reserved system defined pp. 12–13)

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_Election
import Definitions.Def_ApprovalCore_HarmonicEntropy_Rule

namespace ApprovalCore.HarmonicEntropy

/-- Lemma 6.4 (p. 13): for every committee `W ⊆ C` there are an optimal payment system
`(r, p)` and a de-reserved system `(r̂, p̂)` derived from it such that for every candidate
`d ∈ W` unsaturated in `(r̂, p̂)` and every voter `i ∈ N_d`:
(a) `p̂_{id} ≥ p̂_{ic}` for every `c ∈ A_i ∩ W`, and (b) `F(r̂_i, p̂_i) = F(r_i, p_i) − p̂_{id}`. -/
theorem lemma_6_4 {n m : ℕ} (I : Instance n m) (q : ℝ)
    (hq₁ : (n : ℝ) / ((I.k : ℝ) + 1) < q) (hq₂ : q ≤ (n : ℝ) / (I.k : ℝ))
    (W : Finset (Fin m)) :
    ∃ rp : PaymentPair n m, IsOptimal I.A q W rp ∧
      ∃ rph : PaymentPair n m, IsDeReserved I.A q W rp rph ∧
        ∀ d, Unsaturated I.A q W rph d → ∀ i ∈ supporters I.A d,
          (∀ c ∈ I.A i ∩ W, rph.2 i d ≥ rph.2 i c) ∧
          harmonicEntropy (voterDist I.A W rph i)
            = harmonicEntropy (voterDist I.A W rp i) - rph.2 i d := by sorry

end ApprovalCore.HarmonicEntropy
