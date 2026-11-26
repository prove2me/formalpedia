-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_finite_jump_energy_lower_on_of_overlap_formula
-- name    : Auto.aux_CuboidNorm.finite_jump_energy_lower_on_of_overlap_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:34.411693+00:00
-- url     : https://prove2.me/theorems/d8b2c88c-5629-5390-a3c4-daa9969d65f0
-- title:
--   aux Cuboid Norm: finite jump energy lower on of overlap formula
-- statement:
--   The exact cuboid-overlap formula controls every finite portion of the
--   integer-lattice jump energy by the corresponding continuous jump energy.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1964-L2025
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1964-L2025

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
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.finite_jump_energy_lower_on_of_overlap_formula {n J : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1) (hεδ : ε ≤ δ)
    (hwidth : ε + δ < 1) (N : Fin (J + 1) → ℕ)
    (hNpos : ∀ q, 0 < N q) (a : Fin n → ZVector n → ℝ)
    (A : Finset (ZVector n)) :
    (ENNReal.ofReal (δ - ε) ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
        ∑ j : Fin J, ∑ k ∈ A,
          ‖aux_integerDiscreteAverage (N j.succ) a k -
            aux_integerDiscreteAverage (N j.castSucc) a k‖ₑ ^ (2 : ℝ) ≤
      ∑ j : Fin J, eLpNorm
        (fun x ↦ ctTwistedAverageAtScale (N j.succ : ℝ) ctUnitIntervalKernel
            (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
            (WithLp.toLp 2 x) -
          ctTwistedAverageAtScale (N j.castSucc : ℝ) ctUnitIntervalKernel
            (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
            (WithLp.toLp 2 x)) 2 volume ^ 2 := by sorry
