-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_8_1
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:29:54.839697+00:00
-- url     : https://prove2.me/theorems/263c46c8-f1cf-48d3-8bcf-9407f8a5cc57
-- title:
--   Lemma 8.1 — common wROT postprocessing
-- statement:
--   There is an absolute $c_0>0$ with the following property. For all $p,q\in[0,1]$ with $p+q<1$ there are $C_{p,q},D_{p,q}>0$ such that for all positive integers $\ell,\lambda$ there is a two-client protocol $Q$ on $K\le C_{p,q}(\ell+\lambda)$ independent $(p,q)$-wROT pairs with two properties. First, against either fixed passively corrupted client, its complete view can be simulated from that client's ideal view of $\ell$ ROT pairs, jointly with both clients' final ROT outputs, with error $c_0 2^{-\lambda}$; that view comprises its initial wROT outputs, revelation flags, private state (hence coins) and transcript. Second, in every execution $Q$ uses at most $D_{p,q}(\ell+\lambda)$ bits. The protocol satisfies the synchronous round-completion condition. The adversary receives its initial wROT revelations before making scheduling decisions.
--
--   Differences from the source:
--   - reading: a two-client protocol → a Protocol with 0 servers whose clients’ inputs are their wROT outputs; reason: a two-client protocol involves no servers
--   - reading: O_{p,q}(ℓ+λ) wROT pairs, error O(2^{−λ}), O_{p,q}(ℓ+λ) additional bits → ∃ K ≤ C_{p,q}(ℓ+λ); error c₀·2^{−λ} with c₀ absolute; at most D_{p,q}(ℓ+λ) bits; reason: the paper’s subscript convention
--   - reading: using O_{p,q}(ℓ+λ) additional bits → in every execution, under every adversary; reason: the count in the proof, O(rMK₀ + M), is deterministic
--   - generalization: the bit bound for executions on independent (p,q)-wROT pairs → the bit bound for every value of the wROT inputs and in every setting; reason: a bound for every input value implies the bound for random inputs
--   - reading: the network model of Section 2 (synchronous private channels; separate send, receive and erase operations; corruption between operations; rushing; permitted scheduling) → `Protocol` / `realExec`: operation-level scheduling and corruption, including receipt from a selected sender; private traffic is hidden; state replacement models erasure, with a separate delivery-gated operation for Figure 5; round deadlines complete the remaining operations; reason: the synchronous private-channel model permits these interleavings; Synchronous records completion of each round for abstract preprocessing and postprocessing protocols
--   - encoding: distributions of protocol executions → discrete distributions (`PMF`); statistical distance is ½‖·‖₁ (`tvPMF`); probabilities and expectations via `probE` / `expectE` (expectation in ℝ≥0∞); reason: every protocol variable is discrete, and on discrete spaces ½‖·‖₁ is the statistical distance
--   - encoding: corrupted client has its initial wROT outputs and revelations → the scheduling strategy receives those outputs, flags and revealed bits before its first decision; reason: the source allows adaptive decisions based on all information initially held by the corrupted client
--   - encoding: two-client protocol in the synchronous network model → Q.Synchronous; reason: the abstract program’s round bound must actually complete all local operations and message deliveries
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 8.1, p. 39 (PDF 41)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Security

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 8.1 (common wROT postprocessing).  The constant of `O(2^{-λ})` is absolute; the
constants of `O_{p,q}(ℓ + λ)` depend only on `p, q`. -/
theorem lemma_8_1 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 → p + q < 1 →
      ∃ Cpq Dpq : ℝ, 0 < Cpq ∧ 0 < Dpq ∧
        ∀ ℓ lam : ℕ, 1 ≤ ℓ → 1 ≤ lam →
          ∃ (K : ℕ) (Q : Protocol 0 (Bits K × Bits K) (Bits K × Bits K) (Bits ℓ × Bits ℓ)
              (Bits ℓ × Bits ℓ)),
            Q.Synchronous ∧ (K : ℝ) ≤ Cpq * (ℓ + lam) ∧
            (∀ P : Client, HybridSim Q p q P (c₀ * (2 : ℝ)⁻¹ ^ lam)) ∧
            ∀ (Aux : Type) (A : Adversary 0 Q.S Aux) (aux : Aux) (a b : Bits K × Bits K)
              (fixed : Option Client),
              probE (Q.realExec 0 A aux a b fixed)
                (fun cfg => Dpq * ((ℓ : ℝ) + lam) < bitsUsed cfg) = 0 := by sorry

end ChoiSemiHonestMPC.OTUpper
