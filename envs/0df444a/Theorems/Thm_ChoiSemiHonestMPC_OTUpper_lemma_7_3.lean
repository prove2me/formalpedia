-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_7_3
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:32:28.98734+00:00
-- url     : https://prove2.me/theorems/3e9460b4-eb50-4e4c-aa6a-0e25ed0fb98d
-- title:
--   Lemma 7.3 — selection and communication tails of Protocol 3
-- statement:
--   Under Section 7.1's parameters, for every adversary, Protocol 3 fails with probability at most $e^{-2K/e}$. Let $V$ be the total number of participants over all $32K$ trials, which is the number of tagged bits sent to Alice. Then $\mathbb EV=32sK$ and $\Pr[V>32K(s+2)]\le(e^2/27)^{32K}$.
--
--   Differences from the source:
--   - reading: the network model of Section 2 (synchronous private channels; separate send, receive and erase operations; corruption between operations; rushing; permitted scheduling) → `Protocol` / `realExec`: operation-level scheduling and corruption, including receipt from a selected sender; private traffic is hidden; state replacement models erasure, with a separate delivery-gated operation for Figure 5; round deadlines complete the remaining operations; reason: the synchronous private-channel model permits these interleavings; Synchronous records completion of each round for abstract preprocessing and postprocessing protocols
--   - generalization: abort/failure and communication bounds stated for the protocol (no adversary named) → stated under every adversary (any scheduling, any server corruptions, any auxiliary input) and in both the adaptive and the fixed-client setting (`fixed : Option Client`); reason: a passive adversary cannot change honest behaviour, so the source bound is the special case of any one adversary
--   - encoding: V = total number of participants over all 32K trials → the number of messages sent by servers to Alice; reason: in Protocol 3 exactly the participants send one tagged bit to Alice per trial and servers send nothing else to her
--   - encoding: Protocol 3 fails → the execution aborts (a client outputs ⊥); reason: Alice’s abort announcement is the only failure
--   - encoding: distributions of protocol executions → discrete distributions (`PMF`); statistical distance is ½‖·‖₁ (`tvPMF`); probabilities and expectations via `probE` / `expectE` (expectation in ℝ≥0∞); reason: every protocol variable is discrete, and on discrete spaces ½‖·‖₁ is the statistical distance
--   - generalization: K a positive integer (Protocol 3 generates K wROT pairs) → every K ∈ ℕ, including K = 0; reason: at K = 0 there are no trials, nothing aborts and V = 0, so all three claims hold trivially; every positive K is an instance
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 7.3, p. 34 (PDF 36)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol3

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 7.3 (selection and communication tails of Protocol 3).  `V` is the total number
of participants over all `32K` trials, i.e. the number of tagged bits sent to Alice. -/
theorem lemma_7_3 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1 / 2) (n K : ℕ)
    (hn : ⌈4 * (s3 α : ℝ) / (1 - 2 * α)⌉₊ ≤ n)
    (Aux : Type) (A : Adversary n (protocol3 α n K).S Aux) (aux : Aux) (fixed : Option Client) :
    probE ((protocol3 α n K).realExec ⌊α * n⌋₊ A aux () () fixed) (protocol3 α n K).aborted ≤
        Real.exp (-(2 * K / Real.exp 1)) ∧
      expectE ((protocol3 α n K).realExec ⌊α * n⌋₊ A aux () () fixed)
          (fun c => (c.log.filter fun e => !e.2.1.isClient && decide (e.2.2.1 = Party.alice)).length) =
        ((32 * s3 α * K : ℕ) : ℝ≥0∞) ∧
      probE ((protocol3 α n K).realExec ⌊α * n⌋₊ A aux () () fixed)
          (fun c => 32 * K * (s3 α + 2) <
            (c.log.filter fun e => !e.2.1.isClient && decide (e.2.2.1 = Party.alice)).length) ≤
        (Real.exp 2 / 27) ^ (32 * K) := by sorry

end ChoiSemiHonestMPC.OTUpper
