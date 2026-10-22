-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_L1_approximation_stability
-- name    : AvramDividend.Classical.levy_condExp_lipschitz_L1_approximation_stability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:01:11.656104+00:00
-- url     : https://prove2.me/theorems/f39dc435-4402-4493-a313-087f3e982d8b
-- title:
--   L1 convergence of conditional Lévy payoffs under integrable approximating starting reserves
-- statement:
--   Fix a spectrally negative Lévy process, s,t, a globally Lipschitz payoff f with constant L, a random starting reserve Z and approximations Z_n. Assume every shifted payoff is integrable, the envelopes L|Z_n−Z| are integrable and their expectations tend to zero. Then the L1 norm of the difference between the two conditional expected shifted payoffs given F_s also tends to zero. This follows immediately by squeezing between zero and the expected envelope using the independent previously Proved integrated conditional Lipschitz contraction theorem. The result is an analytic convergence bridge for passing finite-state Markov identities to general integrable past-measurable random reserves, conditional on constructing the finite-state approximations. It does not assume an optional-stopping theorem or establish an arbitrary C² generator identity. Publication retry following authoritative ACCEPTED/Proved of the prerequisite levy_condExp_lipschitz_integral_bound, candidate 12813, submission e2c30965-7134-4975-a162-99bf70be05e7; the first authoring request was rejected solely because the prerequisite was then Open. The mathematical statement is unchanged.
-- source:
--   Pinned squeeze_zero exact signature and (dependency-gated) levy_condExp_lipschitz_integral_bound; elementary nonnegative integral. The required Prove2Me prerequisite is now Proved at target 91c3bead-3b00-4948-9e03-b1b7cf1b88d2.

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_integral_bound

open Filter MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_condExp_lipschitz_L1_approximation_stability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z : Ω → ℝ) (Zn : ℕ → Ω → ℝ)
    (hZ : Integrable (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hZn : ∀ n, Integrable
      (fun ω => f (Zn n ω + (X.X t ω - X.X s ω))) P)
    (hDom : ∀ n, Integrable (fun ω => L * |Zn n ω - Z ω|) P)
    (hlim : Tendsto (fun n : ℕ =>
      ∫ ω, L * |Zn n ω - Z ω| ∂P) atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, |(P[(fun η =>
            f (Zn n η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
          (P[(fun η =>
            f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ∂P)
      atTop (nhds 0) := by sorry
