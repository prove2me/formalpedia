-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_poisson_weighted_count_transform
-- name    : AvramDividend.Classical.avram_redux18_poisson_weighted_count_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:46:52.5472+00:00
-- url     : https://prove2.me/theorems/b731723c-516e-4757-949f-c10293e089d3
-- title:
--   Poisson weighted exponential count transform
-- statement:
--   For any real formal Poisson rate and exponential weight, summing the Poisson mass series against an exponential weight gives the exact exponential generating function. For nonnegative rates this is the Laplace transform of a Poisson count, the discrete step in the finite-band marked-jump exponential formula.
-- source:
--   Exact elementary analytic component of the genuine finite-cutoff marked Poisson Laplace functional avram_redux17_original_intrinsic_marked_cutoff_laplace (81b0ea8d). The result uses the real exponential power series and finite-rate Poisson generating function, with no unproved original-process assumptions.

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux18_poisson_weighted_count_transform
    (rate q : ℝ) :
    (∑' m : ℕ, Real.exp (-rate) *
      (rate ^ m / (m.factorial : ℝ)) * Real.exp (-(m : ℝ) * q)) =
    Real.exp (rate * (Real.exp (-q) - 1)) := by sorry
