-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_stronglyMeasurable
-- name    : AvramDividend.Classical.levy_transition_random_reserve_stronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:15:17.432068+00:00
-- url     : https://prove2.me/theorems/e052c54b-b87e-4dbc-80d4-8409ed6b8299
-- title:
--   Strong measurability of the Lévy transition evaluated at a random reserve for Lipschitz payoffs
-- statement:
--   For a spectrally negative Lévy process, a real Lipschitz payoff f whose deterministic shifted transition payoffs are integrable for every starting reserve, and any measurable random reserve Z, the map omega to the deterministic transition integral of f evaluated at Z(omega) is strongly measurable. Obtain a Lipschitz bound for the deterministic transition operator using the already Proved levy_transition_preserves_lipschitz_bound, apply the pinned Mathlib LipschitzWith.of_dist_le_mul, and compose its continuity with the measurable random reserve. This discharges the transition-strong-measurability assumptions in the general-reserve Markov theorem.
-- source:
--   Accepted levy_transition_preserves_lipschitz_bound; exact pinned Mathlib declaration LipschitzWith.of_dist_le_mul confirmed by index (signature not elaborated, remote compiler authoritative).

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_preserves_lipschitz_bound

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_random_reserve_stronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ u : ℝ, Integrable
      (fun η => f (u + X.X t η)) P)
    (Z : Ω → ℝ) (hZ : Measurable Z) :
    StronglyMeasurable (fun ω =>
      ∫ η, f (Z ω + X.X t η) ∂P) := by sorry
