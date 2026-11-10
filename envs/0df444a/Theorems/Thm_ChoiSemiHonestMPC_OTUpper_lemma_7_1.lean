-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_7_1
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:32:21.768738+00:00
-- url     : https://prove2.me/theorems/d9c91e1a-17e4-42ce-99c3-65ce5a160c54
-- title:
--   Lemma 7.1 — wROT guarantee of Protocol 3
-- statement:
--   There is an absolute constant $c>0$ with the following property. For every $0\le\alpha<1/2$ there is $D_\alpha>0$ such that for $n\ge\lceil 4s/(1-2\alpha)\rceil$ and $K\ge1$, Protocol 3 aborts with probability at most $e^{-cK}$. For either fixed corrupted client and every passive adversary adaptively corrupting at most $\lfloor\alpha n\rfloor$ servers, the view is simulable from $K$ independent wROT pairs with both revelation probabilities $\alpha+(1-2\alpha)/4$ and error $e^{-cK}$. The communication is at most $D_\alpha K$ bits in expectation and exceeds it with probability at most $e^{-cK}$.
--
--   Differences from the source:
--   - reading: the network model of Section 2 (synchronous private channels; separate send, receive and erase operations; corruption between operations; rushing; permitted scheduling) → `Protocol` / `realExec`: operation-level scheduling and corruption, including receipt from a selected sender; private traffic is hidden; state replacement models erasure, with a separate delivery-gated operation for Figure 5; round deadlines complete the remaining operations; reason: the synchronous private-channel model permits these interleavings; Synchronous records completion of each round for abstract preprocessing and postprocessing protocols
--   - encoding: bit communication (total message length; encodings unspecified) → messages are bit strings with fixed-width binary encodings: counts and labels with `Nat.size n` bits, the index share with `Nat.size Z` bits, block indices with `Nat.size H` bits, tags with ⌈log₂(s(s−1))⌉ bits, one-bit announcements; empty program sends are padded to one zero bit, so actual wire messages all contain at least one bit; reason: the paper fixes no encoding; these are the natural fixed-width encodings its counts assume
--   - reading: e^{−Ω(K)} → exp(−c·K) for one constant c > 0 that is absolute (chosen before α), valid for every admissible n and K; reason: the paper's notation paragraph (p. 12): subscripts list the parameters the implicit constants may depend on
--   - reading: Protocol 3 generating K wROT pairs → K ≥ 1; reason: K is the number of generated pairs, positive as in Section 5.1 and in Theorem 8.3 (K = ⌈C_α(ℓ+λ)⌉)
--   - generalization: abort/failure and communication bounds stated for the protocol (no adversary named) → stated under every adversary (any scheduling, any server corruptions, any auxiliary input) and in both the adaptive and the fixed-client setting (`fixed : Option Client`); reason: a passive adversary cannot change honest behaviour, so the source bound is the special case of any one adversary
--   - encoding: distributions of protocol executions → discrete distributions (`PMF`); statistical distance is ½‖·‖₁ (`tvPMF`); probabilities and expectations via `probE` / `expectE` (expectation in ℝ≥0∞); reason: every protocol variable is discrete, and on discrete spaces ½‖·‖₁ is the statistical distance
--   - encoding: server labels [n] = {1,…,n}; positions and tags counted from 1 → `Fin n` = {0,…,n−1}; positions and tags counted from 0; reason: relabelling by −1 changes no instance
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 7.1, p. 31 (PDF 33)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol3

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 7.1 (wROT guarantee of Protocol 3).  The constant `c` of `e^{-Ω(K)}` is
absolute; the communication constant depends only on `α`. -/
theorem lemma_7_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
      ∃ Dα : ℝ, 0 < Dα ∧
        ∀ n K : ℕ, ⌈4 * (s3 α : ℝ) / (1 - 2 * α)⌉₊ ≤ n → 1 ≤ K →
          (∀ (Aux : Type) (A : Adversary n (protocol3 α n K).S Aux) (aux : Aux)
              (fixed : Option Client),
            probE ((protocol3 α n K).realExec ⌊α * n⌋₊ A aux () () fixed)
                (protocol3 α n K).aborted ≤ Real.exp (-(c * K))) ∧
          (∀ P : Client, FixedClientSim (protocol3 α n K) ⌊α * n⌋₊ P
            (α + (1 - 2 * α) / 4) (α + (1 - 2 * α) / 4) (Real.exp (-(c * K)))) ∧
          ∀ (Aux : Type) (A : Adversary n (protocol3 α n K).S Aux) (aux : Aux)
            (fixed : Option Client),
            expectE ((protocol3 α n K).realExec ⌊α * n⌋₊ A aux () () fixed) bitsUsed ≤
                ENNReal.ofReal (Dα * K) ∧
              probE ((protocol3 α n K).realExec ⌊α * n⌋₊ A aux () () fixed)
                (fun cfg => Dα * K < bitsUsed cfg) ≤ Real.exp (-(c * K)) := by sorry

end ChoiSemiHonestMPC.OTUpper
