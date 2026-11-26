-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_finite_box_bound_of_finite_sum_cancelled
-- name    : Auto.aux_ErgodicBox.finite_box_bound_of_finite_sum_cancelled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:44:51.655802+00:00
-- url     : https://prove2.me/theorems/91a42b12-807b-415e-9756-d5d915c0e5cf
-- title:
--   aux Ergodic Box: finite box bound of finite sum cancelled
-- statement:
--   Most local finite-box form of the ergodic-to-discrete reduction.  The
--   input is only the finite inner-box sum of discrete jumps; no global discrete
--   jump energy and no finite-support theorem for that energy are used.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2844-L2914
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2844-L2914

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

theorem Auto.aux_ErgodicBox.finite_box_bound_of_finite_sum_cancelled
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {n J M : ℕ}
    (hM : 0 < M)
    (T : (Fin n → ℕ) → X → X)
    (hT : ∀ k ∈ box n (M + M),
      MeasurePreserving (T k) μ μ)
    (p : Fin n → ℝ≥0∞) (N : Fin (J + 1) → ℕ)
    (f : Fin n → X → ℝ) (hf : ∀ i, MemLp (f i) (p i) μ)
    (hp0 : ∀ i, p i ≠ 0) (hptop : ∀ i, p i ≠ ∞)
    (hpreal : ∀ i, 0 < (p i).toReal)
    (hqsum : ∑ i, 2 / (p i).toReal = 1)
    (a : Fin (J + 1) → X → ℝ) (d : Fin J → X → ℝ)
    (hd : ∀ j, AEStronglyMeasurable (d j) μ)
    (hjump : ∀ j x, d j x = a j.succ x - a j.castSucc x)
    (A : ℝ≥0∞)
    (hlocal : ∀ x, ∑ j : Fin J, ∑ k ∈ box n M,
      ‖aux_discreteAverage (N j.succ)
          (fun i ↦ truncOrbit (box n (M + M)) T (f i) x) k -
        aux_discreteAverage (N j.castSucc)
          (fun i ↦ truncOrbit (box n (M + M)) T (f i) x) k‖ₑ
        ^ (2 : ℕ) ≤
        A * ∏ i, eLpNorm
          (truncOrbit (box n (M + M)) T (f i) x)
            (p i) Measure.count ^ 2)
    (haverage : ∀ (x : X) (k : Fin n → ℕ) (q : Fin (J + 1)),
      k ∈ box n M →
      aux_discreteAverage (N q)
          (fun i ↦ truncOrbit (box n (M + M)) T (f i) x) k =
        a q (T k x)) :
    ∑ j, eLpNorm (d j) 2 μ ^ 2 ≤
      A * ((2 ^ n : ℕ) : ℝ≥0∞) * ∏ i, eLpNorm (f i) (p i) μ ^ 2 := by sorry
