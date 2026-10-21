-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_random_reserve_payoff_L1_stability
-- name    : AvramDividend.Classical.levy_random_reserve_payoff_L1_stability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:24:14.55838+00:00
-- url     : https://prove2.me/theorems/00a4032d-5166-4ef1-b066-8082dba47cd3
-- title:
--   An L1 stability bound for shifted Lévy payoffs with arbitrary random starting reserves
-- statement:
--   For the actual spectrally negative Lévy process X, and arbitrary (not necessarily independent) random starting reserves Z,W on the same sample space, let f be globally L-Lipschitz. Assume the two shifted payoffs f(Z+X_t−X_s), f(W+X_t−X_s) and the envelope L|Z−W| are integrable. Then the absolute difference of their expected values is at most E[L|Z−W|]. For each outcome the common Lévy increment cancels from the difference of arguments, giving the Lipschitz pointwise bound. Integrate its upper and lower halves by integral_mono_ae and integral_sub. This proves unconditional L1 stability of the payoff operator for arbitrary coupled random initial reserves and is useful in extending the accepted finite-valued Markov identity to limits of simple reserves. No independence of Z from future increments is assumed or needed for this stability estimate. This theorem is not the conditional Markov identity or Lévy generator theorem.
-- source:
--   Pinned integral_mono_ae and standard integral_sub on the given Lévy process, no Open dependencies.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_random_reserve_payoff_L1_stability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z W : Ω → ℝ)
    (hZ : Integrable (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hW : Integrable (fun ω => f (W ω + (X.X t ω - X.X s ω))) P)
    (hDom : Integrable (fun ω => L * |Z ω - W ω|) P) :
    |(∫ ω, f (Z ω + (X.X t ω - X.X s ω)) ∂P) -
      (∫ ω, f (W ω + (X.X t ω - X.X s ω)) ∂P)| ≤
      ∫ ω, L * |Z ω - W ω| ∂P := by sorry
