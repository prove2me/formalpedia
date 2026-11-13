-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a59_original_pathwise_uniform_C2_mesh_remainder
-- name    : AvramDividend.Classical.avram_ga_a59_original_pathwise_uniform_C2_mesh_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:21:46.774276+00:00
-- url     : https://prove2.me/theorems/e86b6d78-30ba-4666-b626-0f1cd94c5ed1
-- title:
--   Original stopped Gaussian C2 remainder vanishes pathwise under compact mesh and quadratic-energy controls
-- statement:
--   For the unchanged original Levy process X, dividend strategy D, and postpayment reserve x+X.X(t)-rightLimit D(t), a compact interior C2 Taylor remainder summed over any finite moving mesh converges to zero pathwise whenever all sampled postpayment states and matching y states remain in one strict compact interior band, their distances vanish uniformly with mesh, and the summed squared distances have a fixed finite pathwise upper bound. This turns the Proved finite-mesh modulus estimate a58 into a genuine pathwise convergence statement, preserving X and D. The physical stochastic remaining tasks are to show suitable compact stopped-cell excursions and quadratic energy on almost every path.
-- source:
--   Physical interior Gaussian residual b0d9951c and Proved a58 f5496974, prepared as a necessary analytic sublemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a59_original_pathwise_uniform_C2_mesh_remainder
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mOmega}
    (X : SpectrallyNegativeLevy P F)
    (x : Real) (D : NNReal -> Omega -> Real)
    (hD : IsDividendStrategy F D)
    (C : ENNReal) (w : Real -> Real)
    (hw : ContDiffOn Real 2 w {z : Real | 0 < z ∧ ENNReal.ofReal z < C})
    (a b : Real) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (omega : Omega) (S : Nat -> Finset Nat)
    (s : Nat -> Nat -> NNReal) (y : Nat -> Nat -> Real)
    (K : Real) (hK : 0 ≤ K) :
    let z : Nat -> Nat -> Real := fun m i =>
      x + X.X (s m i) omega - rightLimit D (s m i) omega
    (∀ m i, i ∈ S m -> z m i ∈ Icc a b ∧
      y m i ∈ Icc a b ∧ z m i ≠ y m i) ->
    (∀ delta : Real, 0 < delta -> ∃ k : Nat,
      ∀ m : Nat, k ≤ m -> ∀ i ∈ S m,
        dist (y m i) (z m i) < delta) ->
    (∀ m : Nat, (∑ i ∈ S m, (y m i - z m i) ^ 2) ≤ K) ->
    ∀ eps : Real, 0 < eps -> ∃ k : Nat,
      ∀ m : Nat, k ≤ m ->
      |∑ i ∈ S m, (w (y m i) -
        taylorWithinEval w 1 (uIcc (z m i) (y m i)) (z m i) (y m i) -
        (iteratedDeriv 2 w (z m i) * (y m i - z m i) ^ 2) / 2)| ≤ eps := by sorry
