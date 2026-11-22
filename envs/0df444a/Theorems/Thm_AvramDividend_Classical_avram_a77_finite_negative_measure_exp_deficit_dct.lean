-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_finite_negative_measure_exp_deficit_dct
-- name    : AvramDividend.Classical.avram_a77_finite_negative_measure_exp_deficit_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:30:32.034037+00:00
-- url     : https://prove2.me/theorems/0cb138f2-200a-4631-bb20-f227501d4c95
-- title:
--   Finite negative Lévy measure exponential deficit dominated convergence for nonpositive Borel step approximants
-- statement:
--   For an arbitrary finite measure on strictly negative real marks, every sequence of measurable nonpositive exponent functions converging pointwise on negative marks to theta*y induces convergence of the real Lévy-measure exponential deficit integrals exp(q_n)-1. The uniform [-1,0] bound and finiteness of the restricted negative measure justify ordinary dominated convergence. This is the deterministic intensity half of the original Avram a77->5b->cc5 physical negative-mark Borel approximation, with all source measure arguments explicit, no artificial Poisson driver and no assumption of the desired full expectation formula.
-- source:
--   Avram original physical negative marked jump Laplace child cc5c4242 under 5b48325d, finite intensity X.nu(Iio0). Uses pinned Mathlib isFiniteMeasure_restrict and tendsto_integral_of_dominated_convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_a77_finite_negative_measure_exp_deficit_dct
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) ≠ ⊤)
    (θ : ℝ) (q : ℕ → ℝ → ℝ)
    (hqMeas : ∀ n, Measurable (q n))
    (hqNonpos : ∀ n y, y < 0 → q n y ≤ 0)
    (hLimit : ∀ y, y < 0 →
      Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) :
    Tendsto
      (fun n => ∫ y in Iio (0 : ℝ), Real.exp (q n y) - 1 ∂ν)
      atTop
      (𝓝 (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂ν)) := by sorry
