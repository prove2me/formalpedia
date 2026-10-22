-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_reserve_comparison
-- name    : AvramDividend.Classical.levy_condExp_lipschitz_reserve_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T10:59:56.561299+00:00
-- url     : https://prove2.me/theorems/1925e057-77da-4bc1-aa72-2c626dbee1e6
-- title:
--   Two-sided conditional expectation domination for Lipschitz Lévy payoffs under different random starting reserves
-- statement:
--   Fix a spectrally negative Lévy process, two possibly coupled random starting reserves Z,W and any real Lipschitz payoff f with constant L. Under integrability of the two shifted Lévy payoffs and the difference envelope L|Z-W|, the conditional expectation given the past filtration of either shifted payoff is almost surely bounded by the conditional expectation of the other payoff plus the envelope. The same Lévy increment cancels pointwise from the two reserve arguments, so this follows from Lipschitz domination and the pinned conditional expectation monotonicity theorem. It provides the conditional analogue of the already Proved unconditional L1 stability theorem and is directly suited to extending finite-valued reserve conditional Markov identities by approximation. It does not assume independence of the random reserves or prove the remaining stopped controlled HJB budget.
-- source:
--   Pinned MeasureTheory.condExp_mono plus pointwise Lipschitz and accepted Lévy-process field interface.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_condExp_lipschitz_reserve_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z W : Ω → ℝ)
    (hZ : Integrable
      (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hW : Integrable
      (fun ω => f (W ω + (X.X t ω - X.X s ω))) P)
    (hDom : Integrable (fun ω => L * |Z ω - W ω|) P) :
    P[(fun ω => f (Z ω + (X.X t ω - X.X s ω))) | 𝓕 s] ≤ᵐ[P]
      P[(fun ω => f (W ω + (X.X t ω - X.X s ω)) +
        L * |Z ω - W ω|) | 𝓕 s] ∧
    P[(fun ω => f (W ω + (X.X t ω - X.X s ω))) | 𝓕 s] ≤ᵐ[P]
      P[(fun ω => f (Z ω + (X.X t ω - X.X s ω)) +
        L * |Z ω - W ω|) | 𝓕 s] := by sorry
