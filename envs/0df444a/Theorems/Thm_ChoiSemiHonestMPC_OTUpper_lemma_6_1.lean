-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_6_1
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:32:39.192507+00:00
-- url     : https://prove2.me/theorems/a777ad5d-e9fd-436d-9677-388fb8cd6ce0
-- title:
--   Lemma 6.1 — wROT guarantee and worst-case communication of Protocol 2
-- statement:
--   Fix $0\le\alpha<1/2$. There are $c_\alpha>0$, $N_0$, $c>0$ and $D_\alpha>0$, depending only on $\alpha$, such that for $n\ge N_0$ and $1\le K\le c_\alpha n/\log_2 n$ the following hold. Protocol 2 aborts with probability at most $e^{-cK}$. For either fixed corrupted client and every passive adversary adaptively corrupting at most $\lfloor\alpha n\rfloor$ servers, the view is simulable from $K$ independent $(p,p)$-wROT pairs with $p=\tfrac12-\tfrac{1-2\alpha}{6(1+2\alpha)}$ and error $e^{-cK}$. In every execution, including aborting ones, it uses at most $D_\alpha(\sqrt{nK\log_2 n}+K\log_2 n)$ bits and $D_\alpha(\sqrt{nK\log_2 n}+K)$ messages.
--
--   Differences from the source:
--   - reading: the network model of Section 2 (synchronous private channels; separate send, receive and erase operations; corruption between operations; rushing; permitted scheduling) → `Protocol` / `realExec`: operation-level scheduling and corruption, including receipt from a selected sender; private traffic is hidden; state replacement models erasure, with a separate delivery-gated operation for Figure 5; round deadlines complete the remaining operations; reason: the synchronous private-channel model permits these interleavings; Synchronous records completion of each round for abstract preprocessing and postprocessing protocols
--   - encoding: bit communication (total message length; encodings unspecified) → messages are bit strings with fixed-width binary encodings: counts and labels with `Nat.size n` bits, the index share with `Nat.size Z` bits, block indices with `Nat.size H` bits, tags with ⌈log₂(s(s−1))⌉ bits, one-bit announcements; empty program sends are padded to one zero bit, so actual wire messages all contain at least one bit; reason: the paper fixes no encoding; these are the natural fixed-width encodings its counts assume
--   - reading: e^{−Ω_α(K)} → exp(−c·K) for one constant c > 0 depending only on α, valid for every admissible n and K; reason: the paper's notation paragraph (p. 12): subscripts list the parameters the implicit constants may depend on
--   - reading: sufficiently large n; c_α > 0 sufficiently small → ∃ N₀ and ∃ cα > 0, depending only on α; reason: the standard meaning of these phrases
--   - encoding: in every execution → with probability 0 of exceeding, under every adversary and in every setting; reason: every execution of the discrete model has positive probability
--   - generalization: abort/failure and communication bounds stated for the protocol (no adversary named) → stated under every adversary (any scheduling, any server corruptions, any auxiliary input) and in both the adaptive and the fixed-client setting (`fixed : Option Client`); reason: a passive adversary cannot change honest behaviour, so the source bound is the special case of any one adversary
--   - encoding: distributions of protocol executions → discrete distributions (`PMF`); statistical distance is ½‖·‖₁ (`tvPMF`); probabilities and expectations via `probE` / `expectE` (expectation in ℝ≥0∞); reason: every protocol variable is discrete, and on discrete spaces ½‖·‖₁ is the statistical distance
--   - encoding: server labels [n] = {1,…,n}; positions and tags counted from 1 → `Fin n` = {0,…,n−1}; positions and tags counted from 0; reason: relabelling by −1 changes no instance
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 6.1, p. 27 (PDF 29)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol2

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 6.1 (wROT guarantee and worst-case communication of Protocol 2). -/
theorem lemma_6_1 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1 / 2) :
    ∃ (cα : ℝ) (N₀ : ℕ) (c Dα : ℝ), 0 < cα ∧ 0 < c ∧ 0 < Dα ∧
      ∀ n K : ℕ, N₀ ≤ n → 1 ≤ K → (K : ℝ) ≤ cα * n / Real.logb 2 n →
        (∀ (Aux : Type) (A : Adversary n (protocol2 α n K).S Aux) (aux : Aux)
            (fixed : Option Client),
          probE ((protocol2 α n K).realExec ⌊α * n⌋₊ A aux () () fixed)
              (protocol2 α n K).aborted ≤ Real.exp (-(c * K))) ∧
        (∀ P : Client, FixedClientSim (protocol2 α n K) ⌊α * n⌋₊ P
          (1 / 2 - (1 - 2 * α) / (6 * (1 + 2 * α))) (1 / 2 - (1 - 2 * α) / (6 * (1 + 2 * α)))
          (Real.exp (-(c * K)))) ∧
        ∀ (Aux : Type) (A : Adversary n (protocol2 α n K).S Aux) (aux : Aux)
          (fixed : Option Client),
          probE ((protocol2 α n K).realExec ⌊α * n⌋₊ A aux () () fixed)
            (fun cfg =>
              Dα * (Real.sqrt (n * K * Real.logb 2 n) + K * Real.logb 2 n) < bitsUsed cfg ∨
              Dα * (Real.sqrt (n * K * Real.logb 2 n) + K) < msgsUsed cfg) = 0 := by sorry

end ChoiSemiHonestMPC.OTUpper
