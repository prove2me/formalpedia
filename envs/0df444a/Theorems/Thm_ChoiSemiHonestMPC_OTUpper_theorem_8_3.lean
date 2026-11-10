-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_theorem_8_3
-- name    : ChoiSemiHonestMPC.OTUpper.theorem_8_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:32:25.663432+00:00
-- url     : https://prove2.me/theorems/c45cdff4-8c9c-4ee6-adb5-8c730a644e35
-- title:
--   Theorem 8.3 — OT upper bounds for Protocols 1–3
-- statement:
--   There is an absolute constant $c_0>0$ with the following property. For every $0\le\alpha<1/2$ there are $C_\alpha>0$, one common postprocessing family, $c'_\alpha>0$, $N_0$ and $D_1,D_3>0$, all depending only on $\alpha$. The postprocessing family is a two-client protocol per $(\ell,\lambda)$ using only the clients' outputs of $K=\lceil C_\alpha(\ell+\lambda)\rceil$ wROT pairs and fresh coins. For positive integers $n,\ell,\lambda$ the following hold, with $t=\lfloor\alpha n\rfloor$ and $f=\sqrt{n(\ell+\lambda)\log_2 n}+(\ell+\lambda)\log_2 n$.
--   1. If $n\ge N_0$ and $\ell+\lambda\le c'_\alpha n/\log_2 n$: Protocol 1 followed by the postprocessing and the three-bit conversion is $c_02^{-\lambda}$-secure for $\ell$ OTs on chosen inputs (Definition 2.1). Under every adversary and every input, it aborts with probability at most $c_02^{-\lambda}$, uses at most $D_1f$ bits in expectation, and exceeds $D_1f$ bits with probability at most $c_02^{-\lambda}$.
--   2. Under the same conditions, the same holds for Protocol 2, except that it never exceeds $D_1f$ bits, including in executions that abort.
--   3. If $n\ge\frac{8}{1-2\alpha}\lceil 4/(1-2\alpha)^2\rceil$: Protocol 3 followed by the same postprocessing and conversion is $c_02^{-\lambda}$-secure, aborts with probability at most $c_02^{-\lambda}$, uses at most $D_3(\ell+\lambda)$ bits in expectation, and exceeds that with probability at most $c_02^{-\lambda}$.
--
--   Differences from the source:
--   - reading: followed by the common postprocessing (defined in the paper only by citing GIMS15 Theorem 3 and HIKN08 Theorem 5) and the conversion of Section 8.2 → ∃ one PostFamily (two-client protocols whose only inputs are the wROT outputs, plus fresh coins), common to the three protocols, followed by the explicit three-bit conversion; reason: the postprocessing is not specified beyond Lemma 8.1; restricting it to two-client protocols on the wROT outputs keeps the theorem about Protocols 1–3 (an unrestricted witness could run its own server-based OT)
--   - reading: O(2^{−λ}); O_α(·); sufficiently large n; sufficiently small c′_α; a sufficiently large C_α → c₀·2^{−λ} with c₀ absolute (chosen before α); Cα, c′, N₀, D₁, D₃ chosen after α and before n, ℓ, λ; reason: the paper’s notation paragraph (p. 12)
--   - reading: Protocol 2 uses the same bound → the same constant D₁; reason: two O_α constants can be replaced by their maximum
--   - reading: the network model of Section 2 (synchronous private channels; separate send, receive and erase operations; corruption between operations; rushing; permitted scheduling) → `Protocol` / `realExec`: operation-level scheduling and corruption, including receipt from a selected sender; private traffic is hidden; state replacement models erasure, with a separate delivery-gated operation for Figure 5; round deadlines complete the remaining operations; reason: the synchronous private-channel model permits these interleavings; Synchronous records completion of each round for abstract preprocessing and postprocessing protocols
--   - encoding: bit communication (total message length; encodings unspecified) → messages are bit strings with fixed-width binary encodings: counts and labels with `Nat.size n` bits, the index share with `Nat.size Z` bits, block indices with `Nat.size H` bits, tags with ⌈log₂(s(s−1))⌉ bits, one-bit announcements; empty program sends are padded to one zero bit, so actual wire messages all contain at least one bit; reason: the paper fixes no encoding; these are the natural fixed-width encodings its counts assume
--   - encoding: computes ℓ OTs on chosen inputs with statistical security error → IsSecure with an online ideal execution for otFun ℓ, comparing (outputs, corrupted client, view); reason: the ideal harness advances the adversary on the disclosed prefix and reveals only the newly corrupted client’s input and prescribed output at that operation
--   - encoding: abort probability; bits in expectation and except with probability; in every execution → for every adversary, input and auxiliary input in the adaptive setting; abort = some client outputs ⊥; "in every execution" = probability 0 of exceeding; reason: every execution of the discrete model has positive probability
--   - encoding: 2^{−λ}; condition n ≥ (8/(1−2α))⌈4/(1−2α)²⌉ → (1/2)^λ with λ written lam; the condition as a real inequality; reason: notation
--   - encoding: distributions of protocol executions → discrete distributions (`PMF`); statistical distance is ½‖·‖₁ (`tvPMF`); probabilities and expectations via `probE` / `expectE` (expectation in ℝ≥0∞); reason: every protocol variable is discrete, and on discrete spaces ½‖·‖₁ is the statistical distance
--   - encoding: server labels [n] = {1,…,n}; positions and tags counted from 1 → `Fin n` = {0,…,n−1}; positions and tags counted from 0; reason: relabelling by −1 changes no instance
--   - encoding: common two-client postprocessing in the synchronous model → PostFamily contains protocols satisfying Synchronous; reason: this records the inherited round-completion requirement for the existentially chosen programs
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Theorem 8.3, p. 43-44 (PDF 45-46)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol2
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol3
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Postprocessing

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Theorem 8.3 (OT upper bounds).  The constant `c₀` of every `O(2^{-λ})` is absolute;
`C_α` (`K = ⌈C_α(ℓ+λ)⌉`), the common postprocessing, `c'_α`, the threshold `N₀` for
"sufficiently large `n`" and the communication constants depend only on `α`. -/
theorem theorem_8_3 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
      ∃ (Cα : ℝ) (post : PostFamily Cα) (c' : ℝ) (N₀ : ℕ) (D₁ D₃ : ℝ),
        0 < Cα ∧ 0 < c' ∧ 0 < D₁ ∧ 0 < D₃ ∧
        -- 1. Protocol 1
        (∀ n ℓ lam : ℕ, 1 ≤ n → N₀ ≤ n → 1 ≤ ℓ → 1 ≤ lam →
          ((ℓ : ℝ) + lam ≤ c' * n / Real.logb 2 n) →
          IsSecure (fullOT (protocol1 α n) Cα post ℓ lam) ⌊α * n⌋₊ (otFun ℓ)
              (c₀ * (2 : ℝ)⁻¹ ^ lam) ∧
          ∀ (Aux : Type) (A : Adversary n (fullOT (protocol1 α n) Cα post ℓ lam).S Aux)
            (aux : Aux) (m : Bits ℓ × Bits ℓ) (c : Bits ℓ),
            probE ((fullOT (protocol1 α n) Cα post ℓ lam).realExec ⌊α * n⌋₊ A aux m c none)
                (fullOT (protocol1 α n) Cα post ℓ lam).aborted ≤ c₀ * (2 : ℝ)⁻¹ ^ lam ∧
            expectE ((fullOT (protocol1 α n) Cα post ℓ lam).realExec ⌊α * n⌋₊ A aux m c none)
                bitsUsed ≤
              ENNReal.ofReal (D₁ * (Real.sqrt (n * ((ℓ : ℝ) + lam) * Real.logb 2 n) +
                ((ℓ : ℝ) + lam) * Real.logb 2 n)) ∧
            probE ((fullOT (protocol1 α n) Cα post ℓ lam).realExec ⌊α * n⌋₊ A aux m c none)
                (fun cfg => D₁ * (Real.sqrt (n * ((ℓ : ℝ) + lam) * Real.logb 2 n) +
                  ((ℓ : ℝ) + lam) * Real.logb 2 n) < bitsUsed cfg) ≤
              c₀ * (2 : ℝ)⁻¹ ^ lam) ∧
        -- 2. Protocol 2
        (∀ n ℓ lam : ℕ, 1 ≤ n → N₀ ≤ n → 1 ≤ ℓ → 1 ≤ lam →
          ((ℓ : ℝ) + lam ≤ c' * n / Real.logb 2 n) →
          IsSecure (fullOT (protocol2 α n) Cα post ℓ lam) ⌊α * n⌋₊ (otFun ℓ)
              (c₀ * (2 : ℝ)⁻¹ ^ lam) ∧
          ∀ (Aux : Type) (A : Adversary n (fullOT (protocol2 α n) Cα post ℓ lam).S Aux)
            (aux : Aux) (m : Bits ℓ × Bits ℓ) (c : Bits ℓ),
            probE ((fullOT (protocol2 α n) Cα post ℓ lam).realExec ⌊α * n⌋₊ A aux m c none)
                (fullOT (protocol2 α n) Cα post ℓ lam).aborted ≤ c₀ * (2 : ℝ)⁻¹ ^ lam ∧
            probE ((fullOT (protocol2 α n) Cα post ℓ lam).realExec ⌊α * n⌋₊ A aux m c none)
                (fun cfg => D₁ * (Real.sqrt (n * ((ℓ : ℝ) + lam) * Real.logb 2 n) +
                  ((ℓ : ℝ) + lam) * Real.logb 2 n) < bitsUsed cfg) = 0) ∧
        -- 3. Protocol 3
        (∀ n ℓ lam : ℕ, 1 ≤ n → 8 / (1 - 2 * α) * ⌈4 / (1 - 2 * α) ^ 2⌉₊ ≤ (n : ℝ) →
          1 ≤ ℓ → 1 ≤ lam →
          IsSecure (fullOT (protocol3 α n) Cα post ℓ lam) ⌊α * n⌋₊ (otFun ℓ)
              (c₀ * (2 : ℝ)⁻¹ ^ lam) ∧
          ∀ (Aux : Type) (A : Adversary n (fullOT (protocol3 α n) Cα post ℓ lam).S Aux)
            (aux : Aux) (m : Bits ℓ × Bits ℓ) (c : Bits ℓ),
            probE ((fullOT (protocol3 α n) Cα post ℓ lam).realExec ⌊α * n⌋₊ A aux m c none)
                (fullOT (protocol3 α n) Cα post ℓ lam).aborted ≤ c₀ * (2 : ℝ)⁻¹ ^ lam ∧
            expectE ((fullOT (protocol3 α n) Cα post ℓ lam).realExec ⌊α * n⌋₊ A aux m c none)
                bitsUsed ≤ ENNReal.ofReal (D₃ * ((ℓ : ℝ) + lam)) ∧
            probE ((fullOT (protocol3 α n) Cα post ℓ lam).realExec ⌊α * n⌋₊ A aux m c none)
                (fun cfg => D₃ * ((ℓ : ℝ) + lam) < bitsUsed cfg) ≤ c₀ * (2 : ℝ)⁻¹ ^ lam) := by sorry

end ChoiSemiHonestMPC.OTUpper
