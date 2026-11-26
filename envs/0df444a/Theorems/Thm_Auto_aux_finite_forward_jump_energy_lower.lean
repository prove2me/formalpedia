-- Prove2me | Theorems.Thm_Auto_aux_finite_forward_jump_energy_lower
-- name    : Auto.aux_finite_forward_jump_energy_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:43:19.010228+00:00
-- url     : https://prove2.me/theorems/43f404b6-9349-5fd4-82f8-cca0e13c3666
-- title:
--   Auto: aux finite forward jump energy lower
-- statement:
--   The Auto construction uses the aux finite forward jump energy lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2212-L2263
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2212-L2263

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_finite_forward_jump_energy_lower {n J : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1) (hεδ : ε ≤ δ)
    (hwidth : ε + δ < 1) (N : Fin (J + 1) → ℕ)
    (hN : StrictMono N) (hNpos : ∀ q, 0 < N q)
    (F : Fin n → (Fin n → ℕ) → ℝ) (A : Finset (Fin n → ℕ)) :
    (ENNReal.ofReal (δ - ε) ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
        ∑ j : Fin J, ∑ k ∈ A,
          ‖aux_discreteAverage (N j.succ) F k -
            aux_discreteAverage (N j.castSucc) F k‖ₑ ^ (2 : ℝ) ≤
      ctEndpointEnergy J (fun q ↦ (N q : ℝ)) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i
          (aux_natToInt (aux_truncate
            (aux_localInputSupport A (N (Fin.last J))) (F i))))) := by sorry
