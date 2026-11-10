-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_5_1
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:31:31.522514+00:00
-- url     : https://prove2.me/theorems/a929a1ae-7b32-4103-a6b4-515403eaf064
-- title:
--   Lemma 5.1 — wROT guarantee of Protocol 1
-- statement:
--   Fix $0\le\alpha<1/2$. There is $c>0$, depending only on $\alpha$, such that for all $n\ge2$ and $1\le K\le c_\alpha n/\log_2 n$, Protocol 1 aborts with probability at most $e^{-cK}$. Moreover, for either fixed corrupted client and every passive adversary adaptively corrupting at most $\lfloor\alpha n\rfloor$ servers, the complete view can be simulated from that client's ideal view of $K$ independent $(p,p)$-wROT pairs, $p=(1+\alpha)/3$, with error $e^{-cK}$.
--
--   Differences from the source:
--   - reading: the network model of Section 2 (synchronous private channels; separate send, receive and erase operations; corruption between operations; rushing; permitted scheduling) → `Protocol` / `realExec`: operation-level scheduling and corruption, including receipt from a selected sender; private traffic is hidden; state replacement models erasure, with a separate delivery-gated operation for Figure 5; round deadlines complete the remaining operations; reason: the synchronous private-channel model permits these interleavings; Synchronous records completion of each round for abstract preprocessing and postprocessing protocols
--   - reading: e^{−Ω_α(K)} → exp(−c·K) for one constant c > 0 depending only on α, valid for every admissible n and K; reason: the paper's notation paragraph (p. 12): subscripts list the parameters the implicit constants may depend on
--   - generalization: abort/failure and communication bounds stated for the protocol (no adversary named) → stated under every adversary (any scheduling, any server corruptions, any auxiliary input) and in both the adaptive and the fixed-client setting (`fixed : Option Client`); reason: a passive adversary cannot change honest behaviour, so the source bound is the special case of any one adversary
--   - encoding: distributions of protocol executions → discrete distributions (`PMF`); statistical distance is ½‖·‖₁ (`tvPMF`); probabilities and expectations via `probE` / `expectE` (expectation in ℝ≥0∞); reason: every protocol variable is discrete, and on discrete spaces ½‖·‖₁ is the statistical distance
--   - encoding: server labels [n] = {1,…,n}; positions and tags counted from 1 → `Fin n` = {0,…,n−1}; positions and tags counted from 0; reason: relabelling by −1 changes no instance
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 5.1, p. 21 (PDF 23)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol1

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 5.1 (wROT guarantee of Protocol 1). -/
theorem lemma_5_1 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ n K : ℕ, 2 ≤ n → 1 ≤ K → (K : ℝ) ≤ cAlpha1 α * n / Real.logb 2 n →
        (∀ (Aux : Type) (A : Adversary n (protocol1 α n K).S Aux) (aux : Aux)
            (fixed : Option Client),
          probE ((protocol1 α n K).realExec ⌊α * n⌋₊ A aux () () fixed)
              (protocol1 α n K).aborted ≤ Real.exp (-(c * K))) ∧
        ∀ P : Client, FixedClientSim (protocol1 α n K) ⌊α * n⌋₊ P
          ((1 + α) / 3) ((1 + α) / 3) (Real.exp (-(c * K))) := by sorry

end ChoiSemiHonestMPC.OTUpper
