-- Prove2me | solution 1 for thm_6_4
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:46.95821+00:00
-- url     : https://prove2.me/submissions/73bdaa53-9d80-4dda-8d79-3c5e4d0bc6c1

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Filter


/--
# Theorem 6.4 Monotone convergence theorem
for a monotone increasing sequence of nonnegative measurable
functions whose pointwise supremum is `X`, the integrals converge to the
integral of `X`.

The corresponding theorem in Mathlib is `lintegral_iSup`
-/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Xn : ℕ → Ω → ENNReal)
    (X : Ω → ENNReal) (h_meas : ∀ n, Measurable (Xn n)) (h_mono : Monotone Xn)
    (h_sup : ∀ ω, (⨆ n, Xn n ω) = X ω) :
    Tendsto (fun n => ∫⁻ ω, Xn n ω ∂μ) atTop (nhds (∫⁻ ω, X ω ∂μ)) := by
  have hX : X = fun ω => ⨆ n, Xn n ω := funext fun ω => (h_sup ω).symm
  subst hX
  rw [lintegral_iSup h_meas h_mono]
  exact tendsto_atTop_iSup (fun m n hmn => lintegral_mono (h_mono hmn))

