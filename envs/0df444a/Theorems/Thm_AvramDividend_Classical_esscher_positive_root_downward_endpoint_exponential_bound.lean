-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_downward_endpoint_exponential_bound
-- name    : AvramDividend.Classical.esscher_positive_root_downward_endpoint_exponential_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:11:39.023249+00:00
-- url     : https://prove2.me/theorems/1fc497ba-5fec-4ced-88dd-a0744a8fea62
-- title:
--   Explicit q-root Esscher downward endpoint Chernoff bound with exponential time decay
-- statement:
--   If φ>0 is the q-root ψφ=q>0, the actual finite-horizon φ-Esscher probability of a downward endpoint X_t≤−b satisfies exp((φ/2)b)Q_t(X_t≤−b)≤exp(−tq/2). This quantitatively controls the terminal negative tail and decays exponentially in both reserve b and elapsed time. It is a rigorous elementary finite-time precursor to the running-infimum maximal estimate and eventual nondefectiveness of the Esscher reflected-infimum law.
-- source:
--   Combine proved exact finite Esscher endpoint Chernoff bound with proved Lévy positive-secant monotonicity ψ(φ/2)≤q/2, rearrange exponent, and use monotonicity of real exponential and ENNReal.ofReal. No global tilted law, derivative assumptions, or Wiener–Hopf formula is used.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_downward_endpoint_chernoff_bound
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.esscher_positive_root_downward_endpoint_exponential_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ b : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp ((φ / 2) * b)) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X t ω - (t : ℝ) * X.ψ φ))))
        {ω : Ω | X.X t ω ≤ -b} ≤
      ENNReal.ofReal (Real.exp (-(t : ℝ) * q / 2)) := by sorry
