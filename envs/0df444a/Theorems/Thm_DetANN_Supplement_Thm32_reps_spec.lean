-- Prove2me | Theorems.Thm_DetANN_Supplement_Thm32_reps_spec
-- name    : DetANN.Supplement.Thm32.reps_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-21T03:40:40.348178+00:00
-- url     : https://prove2.me/theorems/65c686ec-eb21-440d-8b31-c2ad0c5e9036
-- title:
--   The repetition count of the signed Hadamard blocks
-- statement:
--   1. For $L,p_0\in\mathbb N$ with $p_0>0$ and $\tau>0$: $\mathrm{numReps}\big(L\tau^2/p_0,\ \tau,\ p_0\big)=L$.
--   2. For $p_0>0$: if $q\,p_0\le L\tau^2$ then $q\le L\tau^2/p_0$.
--   3. For $\tau>0$: if $2^{m'}\tau^2<c$ for all $m'<m$, then $2^m\le\max\big(1,\ 2c/\tau^2\big)$.
--
--   So the $L$ chosen by `pre` is the repetition count $\mathrm{numReps}(C_0',\tau,p_0)$ of a constant $C_0'\ge q$, and $L\le\max(1,2q\,p_0/\tau^2)$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the construction of §6.1, p.14, and Lemma 6.2). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_Supplement_PreDedup

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

/-- **The repetition count.** `numReps (L·τ²/p₀) τ p₀ = L`; this constant is `≥ q` when `q·p₀ ≤ L·τ²`;
and the least power of two `2^m` with `2^m·τ² ≥ c` is at most `max 1 (2c/τ²)`. -/
theorem reps_spec :
    (∀ (L p0 : ℕ) (τ : ℝ), 0 < τ → 0 < p0 → numReps ((L : ℝ) * τ ^ 2 / p0) τ p0 = L) ∧
    (∀ (L p0 : ℕ) (τ q : ℝ), 0 < p0 → q * p0 ≤ L * (τ * τ) → q ≤ (L : ℝ) * τ ^ 2 / p0) ∧
    (∀ (m : ℕ) (c τ : ℝ), 0 < τ → (∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < c) →
      (2 : ℝ) ^ m ≤ max 1 (2 * c / (τ * τ))) := by sorry

end DetANN.Supplement.Thm32
