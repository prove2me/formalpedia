-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_finite_attained_times_strict
-- name    : AvramDividend.Classical.firstUpcrossing_finite_attained_times_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:49:54.208478+00:00
-- url     : https://prove2.me/theorems/f0a7507b-c992-48fd-9c12-22868176b3f8
-- title:
--   Strict separation of finite upward-record times at different positive levels
-- statement:
--   On a spectrally negative Lévy path, the finite first strict-passage times of two record levels b<c with b>=0 are strictly ordered. The accepted weak monotonicity of finite passage clocks gives u<=v; if they coincided, the accepted no-positive-overshoot theorem would force the path to equal both b and c at the same time. This rules out zero-duration renewal cells for positive record increments, independently of the strong-Markov and q-scale exit-transform identities.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, reflected running-supremum renewal cells. Follows from proved firstUpcrossing_finite_attained_times_mono and firstUpcrossing_value_eq_threshold at the pinned revision.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_finite_attained_times_mono
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.firstUpcrossing_finite_attained_times_strict
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b c : ℝ) (hb : 0 ≤ b) (hbc : b < c)
    (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞))) : (u : ℝ) < (v : ℝ) := by sorry
