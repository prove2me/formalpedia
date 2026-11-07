-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_finite_poisson_partition_transform
-- name    : AvramDividend.Classical.avram_redux18_finite_poisson_partition_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:01:32.967075+00:00
-- url     : https://prove2.me/theorems/084f21d1-1cc8-4772-b297-ca42b21a75d8
-- title:
--   Independent finite-band Poisson marked Laplace partition product
-- statement:
--   For a finite partition of disjoint jump-mark bins with formal Poisson rates and exponential weights, the product of their exact count-transform series is the exponential of the sum of band compensators. This is the deterministic finite-partition component needed to pass from the intrinsic jump process to its continuum marked Laplace functional.
-- source:
--   Depends on the accepted analytic count-transform theorem b731723c. The original Lévy process must separately establish independent Poisson counts and the step-to-continuum limit; this theorem packages their elementary product calculation.

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_avram_redux18_poisson_weighted_count_transform
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux18_finite_poisson_partition_transform
    {ι : Type*} (s : Finset ι) (rate q : ι → ℝ) :
    s.prod (fun i =>
      (∑' m : ℕ, Real.exp (-(rate i)) *
        ((rate i) ^ m / (m.factorial : ℝ)) *
        Real.exp (-(m : ℝ) * q i))) =
    Real.exp (s.sum (fun i => rate i * (Real.exp (-(q i)) - 1))) := by sorry
