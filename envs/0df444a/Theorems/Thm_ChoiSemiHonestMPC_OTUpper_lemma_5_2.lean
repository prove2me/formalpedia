-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_5_2
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:30:52.287871+00:00
-- url     : https://prove2.me/theorems/91ab56b4-bf13-40c8-b04d-6c8fd966db9e
-- title:
--   Lemma 5.2 — availability and communication of Protocol 1
-- statement:
--   Fix $0\le\alpha<1/2$. There are $D_\alpha,c_\alpha>0$, depending only on $\alpha$, such that for all $n\ge2$ and $1\le K\le c_\alpha n/\log_2 n$ (with Section 5.1's $c_\alpha$), every adversary and every setting, Protocol 1 satisfies the following. The probability that packing or record selection fails is at most $e^{-nu/8}+e^{-n/8}+2e^{-(2d-1)K/4}$. The bit communication is at most $D_\alpha(\sqrt{nK\log_2 n}+K\log_2 n+\log_2 n)$ in expectation, and exceeds that bound with probability at most $e^{-c_\alpha K}$.
--
--   Differences from the source:
--   - reading: the network model of Section 2 (synchronous private channels; separate send, receive and erase operations; corruption between operations; rushing; permitted scheduling) → `Protocol` / `realExec`: operation-level scheduling and corruption, including receipt from a selected sender; private traffic is hidden; state replacement models erasure, with a separate delivery-gated operation for Figure 5; round deadlines complete the remaining operations; reason: the synchronous private-channel model permits these interleavings; Synchronous records completion of each round for abstract preprocessing and postprocessing protocols
--   - encoding: bit communication (total message length; encodings unspecified) → messages are bit strings with fixed-width binary encodings: counts and labels with `Nat.size n` bits, the index share with `Nat.size Z` bits, block indices with `Nat.size H` bits, tags with ⌈log₂(s(s−1))⌉ bits, one-bit announcements; empty program sends are padded to one zero bit, so actual wire messages all contain at least one bit; reason: the paper fixes no encoding; these are the natural fixed-width encodings its counts assume
--   - generalization: abort/failure and communication bounds stated for the protocol (no adversary named) → stated under every adversary (any scheduling, any server corruptions, any auxiliary input) and in both the adaptive and the fixed-client setting (`fixed : Option Client`); reason: a passive adversary cannot change honest behaviour, so the source bound is the special case of any one adversary
--   - reading: e^{−Ω_α(K)} → exp(−c·K) for one constant c > 0 depending only on α, valid for every admissible n and K; reason: the paper's notation paragraph (p. 12): subscripts list the parameters the implicit constants may depend on
--   - encoding: packing or record selection fails → the execution aborts (a client outputs ⊥); reason: in Protocol 1 these are the only aborts
--   - reading: O_α(…) in expectation and except with probability e^{−Ω_α(K)} → one constant Dα for both the expectation and the tail bound; reason: two O_α constants can be replaced by their maximum
--   - encoding: distributions of protocol executions → discrete distributions (`PMF`); statistical distance is ½‖·‖₁ (`tvPMF`); probabilities and expectations via `probE` / `expectE` (expectation in ℝ≥0∞); reason: every protocol variable is discrete, and on discrete spaces ½‖·‖₁ is the statistical distance
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 5.2, p. 21-22 (PDF 23-24)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol1

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 5.2 (availability and communication of Protocol 1). -/
theorem lemma_5_2 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1 / 2) :
    ∃ Dα cα : ℝ, 0 < Dα ∧ 0 < cα ∧
      ∀ n K : ℕ, 2 ≤ n → 1 ≤ K → (K : ℝ) ≤ cAlpha1 α * n / Real.logb 2 n →
        ∀ (Aux : Type) (A : Adversary n (protocol1 α n K).S Aux) (aux : Aux)
          (fixed : Option Client),
          probE ((protocol1 α n K).realExec ⌊α * n⌋₊ A aux () () fixed)
              (protocol1 α n K).aborted ≤
            Real.exp (-(n * u1 α n K / 8)) + Real.exp (-((n : ℝ) / 8)) +
              2 * Real.exp (-((2 * (d1 α : ℝ) - 1) * K / 4)) ∧
          expectE ((protocol1 α n K).realExec ⌊α * n⌋₊ A aux () () fixed) bitsUsed ≤
            ENNReal.ofReal (Dα * (Real.sqrt (n * K * Real.logb 2 n) + K * Real.logb 2 n +
              Real.logb 2 n)) ∧
          probE ((protocol1 α n K).realExec ⌊α * n⌋₊ A aux () () fixed)
              (fun c => Dα * (Real.sqrt (n * K * Real.logb 2 n) + K * Real.logb 2 n +
                Real.logb 2 n) < bitsUsed c) ≤
            Real.exp (-(cα * K)) := by sorry

end ChoiSemiHonestMPC.OTUpper
