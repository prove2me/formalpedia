-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_section_6_attainment
-- name    : ApprovalCore.HarmonicEntropy.section_6_attainment
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:42:48.869015+00:00
-- url     : https://prove2.me/theorems/aa1abd86-f7dc-4d7c-b5a2-1a9690c0bf5b
-- title:
--   §6, footnote 6 — $P_{124}(W)$ is non-empty and compact and the maximum defining $V(W)$ is attained
-- statement:
--   Throughout, the standing assumption of p. 4 is in force: $\frac{n}{k+1} < q \le \frac{n}{k}$.
--   For every committee $W \subseteq C$, the set $P_{124}(W)$ of payment systems satisfying (P1), (P2), (P4) is non-empty (the system with $r_i = 1$ and all payments $0$ belongs to it) and compact, and the maximum
--   $$V(W) = \max_{(r,p) \in P_{124}(W)} \sum_{i \in N} F(r_i, p_i)$$
--   is attained: the set of values $\{\sum_i F(r_i,p_i) : (r,p) \in P_{124}(W)\}$ has a greatest element, and it equals $V(W)$.
--
--   **Formalization Note.** Compactness is in $\mathbb R^n \times \mathbb R^{n\times m}$ (the payments off $A_i \cap W$ are fixed to $0$). "Attained" is `IsGreatest (image) (V A q W)`, which makes the `sSup` in the definition of $V$ a genuine maximum.
--
--   Differences from the source:
--
--   - encoding: N = [n], C = {c_1, …, c_m}, k ∈ [m − 1], approval sets A_i ⊆ C → Instance n m: voters Fin n, candidates Fin m, A : Fin n → Finset (Fin m), 1 ≤ k and k + 1 ≤ m; reason: same instances; k ∈ [m − 1] is 1 ≤ k ≤ m − 1, i.e. 1 ≤ k and k + 1 ≤ m
--   - encoding: payments p_ic only for approved winners c ∈ A_i ∩ W → p : Fin n → Fin m → ℝ with p i c = 0 for c ∉ A_i ∩ W, imposed by IsPaymentSystem in every P-set; reason: the forced zeros never enter (P1), (P2), (P4) or a voter's distribution, so the payment systems are the paper's
--   - encoding: V(W) = max over P124(W) of ∑_i F(r_i, p_i) → V = sSup of the image of P124(W) under ∑_i F(r_i, p_i); reason: the supremum is the paper's maximum once it is attained, which is the milestone section_6_attainment (IsGreatest)
--   - encoding: P124(W) compact (as a set of vectors (r, p)) → IsCompact in (Fin n → ℝ) × (Fin n → Fin m → ℝ); reason: the extra coordinates p_ic, c ∉ A_i ∩ W, are fixed to 0, so the set is homeomorphic to the paper's
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 11 (PDF 12), §6 and footnote 6

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_Election
import Definitions.Def_ApprovalCore_HarmonicEntropy_Rule

namespace ApprovalCore.HarmonicEntropy

/-- §6 and footnote 6 (p. 11): under the standing quota assumption, for every committee
`W ⊆ C`, `P124(W)` is non-empty and compact and the maximum defining `V(W)` is attained:
`V(W)` is the greatest value of `∑_i F(r_i, p_i)` over `P124(W)`. -/
theorem section_6_attainment {n m : ℕ} (I : Instance n m) (q : ℝ)
    (hq₁ : (n : ℝ) / ((I.k : ℝ) + 1) < q) (hq₂ : q ≤ (n : ℝ) / (I.k : ℝ))
    (W : Finset (Fin m)) :
    (P124 I.A q W).Nonempty ∧ IsCompact (P124 I.A q W) ∧
      IsGreatest (totalEntropy I.A W '' P124 I.A q W) (V I.A q W) := by sorry

end ApprovalCore.HarmonicEntropy
