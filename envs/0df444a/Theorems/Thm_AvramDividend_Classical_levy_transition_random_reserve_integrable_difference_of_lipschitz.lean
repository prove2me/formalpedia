-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_integrable_difference_of_lipschitz
-- name    : AvramDividend.Classical.levy_transition_random_reserve_integrable_difference_of_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:32:46.982149+00:00
-- url     : https://prove2.me/theorems/38e78ba9-e9f8-4cf7-a4b5-3709d8831010
-- title:
--   Integrability of random-reserve Lévy transition differences from an integrable Lipschitz envelope
-- statement:
--   Let f be a Lipschitz payoff and let its deterministic Lévy transition integral exist integrably for all starting states. For measurable random reserves Z1 and Z2, if the Lipschitz constant times the absolute state difference is integrable, the difference of the two random-reserve transition expectations is integrable. Use the separately established strong measurability of the random-reserve transition, the already Proved preservation of Lipschitz constants, and the Mathlib dominated Integrable.mono lemma. This removes the explicit hTDiff premise in the general-reserve conditional Markov convergence theorem.
-- source:
--   Proved levy_transition_preserves_lipschitz_bound, dependency-gated levy_transition_random_reserve_stronglyMeasurable target e052c54b-b87e-4dbc-80d4-8409ed6b8299 candidate 12923 pending. Pinned Integrable.mono available in index.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_preserves_lipschitz_bound
import Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_stronglyMeasurable

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_random_reserve_integrable_difference_of_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ u : ℝ, Integrable
      (fun η => f (u + X.X t η)) P)
    (Z₁ Z₂ : Ω → ℝ) (hZ₁ : Measurable Z₁)
    (hZ₂ : Measurable Z₂)
    (hDom : Integrable (fun ω => L * |Z₁ ω - Z₂ ω|) P) :
    Integrable (fun ω =>
      (∫ η, f (Z₁ ω + X.X t η) ∂P) -
      (∫ η, f (Z₂ ω + X.X t η) ∂P)) P := by sorry
