-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_realErgodicJumpEnergy_of_finite_sum
-- name    : Auto.aux_ErgodicBox.realErgodicJumpEnergy_of_finite_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:45:05.457873+00:00
-- url     : https://prove2.me/theorems/53fece7c-ca6b-59fe-95e2-01ec660b6251
-- title:
--   aux Ergodic Box: real Ergodic Jump Energy of finite sum
-- statement:
--   The aux Ergodic Box construction uses the real Ergodic Jump Energy of finite sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2983-L3051
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2983-L3051

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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.realErgodicJumpEnergy_of_finite_sum
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {n J : ℕ}
    (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, 1 < p i ∧ p i < ∞)
    (hsum : (∑ i, ((p i)⁻¹).toReal) = 1 / 2)
    (S : ErgodicSystem X μ n) (N : Fin (J + 1) → ℕ)
    (hN : StrictMono N) (hNpos : ∀ j, 0 < N j)
    (f : Fin n → X → ℝ) (hf : ∀ i, MemLp (f i) (p i) μ)
    (A : ℝ≥0∞)
    (hlocal : ∀ x, ∑ j : Fin J,
      ∑ k ∈ box n (N (Fin.last J)),
        ‖aux_discreteAverage (N j.succ)
            (fun i ↦ truncOrbit
              (box n (N (Fin.last J) + N (Fin.last J)))
              (aux_orbit S.transformation) (f i) x) k -
          aux_discreteAverage (N j.castSucc)
            (fun i ↦ truncOrbit
              (box n (N (Fin.last J) + N (Fin.last J)))
              (aux_orbit S.transformation) (f i) x) k‖ₑ ^ (2 : ℝ) ≤
        A * ∏ i, eLpNorm
          (truncOrbit
            (box n (N (Fin.last J) + N (Fin.last J)))
            (aux_orbit S.transformation) (f i) x)
          (p i) Measure.count ^ 2) :
    realErgodicJumpEnergy S N f ≤
      A * ((2 ^ n : ℕ) : ℝ≥0∞) * ∏ i, eLpNorm (f i) (p i) μ ^ 2 := by sorry
