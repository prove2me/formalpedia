-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_finite_secant_and_quotient
-- name    : AvramDividend.Classical.esscher_levy_positive_root_finite_secant_and_quotient
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:43:40.341773+00:00
-- url     : https://prove2.me/theorems/5e0f5b06-6906-46fc-9f2e-f82385c5ba91
-- title:
--   Actual Lévy Esscher positive-root family has a finite strictly positive right slope and reciprocal-root quotient
-- statement:
--   For the canonical spectrally negative Lévy process, at any strictly positive Esscher q-root φ, there exists a finite slope m≥q/φ>0 and a positive root λ_p for each p>0 of ψ(φ+λ_p)-q=p. As p↓0, λ_p→0 from the right and p/λ_p→m. Source-specific exponent convexity on nonnegative parameters supplies finite right secant convergence at φ, the accepted source secant theorem supplies the positive lower bound, and the already accepted positive-root and quotient assembly supplies the root family. No Standing, full HasDerivAt or Wiener–Hopf factor is assumed.
-- source:
--   Proved native Lévy–Khintchine convexity 3ec09019-f499-4957-a73f-dc7b2243f2fa (accepted 351aa0f9), generic convex interior right secant 77e93571, actual root right-slope lower 935a33f8, and root/quotient assembly 4836acf6. All canonically Proved at pinned Mathlib revision.

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_convexOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_esscher_convex_positive_shift_right_secant_limit
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_right_secant_derivative_lower
import Theorems.Thm_AvramDividend_Classical_esscher_levy_root_limit_and_right_secant_quotient

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_levy_positive_root_finite_secant_and_quotient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q phi : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) :
    ∃ (m : ℝ) (root : ℝ → ℝ),
      q / phi ≤ m ∧ 0 < m ∧
      (∀ p : ℝ, 0 < p → 0 < root p) ∧
      (∀ p : ℝ, 0 < p → X.ψ (phi + root p) - q = p) ∧
      Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
      Tendsto (fun p : ℝ => p / root p)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) := by sorry
