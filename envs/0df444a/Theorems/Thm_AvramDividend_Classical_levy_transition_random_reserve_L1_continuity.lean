-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_L1_continuity
-- name    : AvramDividend.Classical.levy_transition_random_reserve_L1_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T13:02:01.050348+00:00
-- url     : https://prove2.me/theorems/32d8f7ee-0b6e-4da8-a987-121c18c4d50c
-- title:
--   L1 stability of the deterministic Lévy transition payoff under random starting-reserve approximation
-- statement:
--   Let f be globally Lipschitz with nonnegative constant L and suppose its deterministic Lévy transition payoffs are integrable at every starting reserve. For random reserves Z_n and Z, assume the absolute differences of their transition expectations and the weighted starting-reserve errors are integrable. If E[L|Z_n−Z|] tends to zero, prove that the ordinary L1 integral of the absolute difference between the transition payoff at Z_n and that at Z also tends to zero. Apply the already Proved deterministic transition Lipschitz bound pointwise at each sample ω, integrate the inequality using integral_mono_ae, and conclude by squeeze_zero. This is the right-hand-side L1 stability bridge required when finite simple-state conditional Markov identities are passed to general integrable starting reserves.
-- source:
--   Proved levy_transition_preserves_lipschitz_bound target 92c50339-afaa-402c-872b-fb8cabe1dff9; pinned integral_mono_ae and squeeze_zero.

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_preserves_lipschitz_bound

open Filter MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_random_reserve_L1_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ u : ℝ, Integrable (fun η => f (u + X.X t η)) P)
    (Zn : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hDiff : ∀ n, Integrable (fun ω =>
      |(∫ η, f (Zn n ω + X.X t η) ∂P) -
        (∫ η, f (Z ω + X.X t η) ∂P)|) P)
    (hDom : ∀ n, Integrable
      (fun ω => L * |Zn n ω - Z ω|) P)
    (hlim : Tendsto (fun n : ℕ =>
      ∫ ω, L * |Zn n ω - Z ω| ∂P)
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ => ∫ ω,
        |(∫ η, f (Zn n ω + X.X t η) ∂P) -
          (∫ η, f (Z ω + X.X t η) ∂P)| ∂P)
      atTop (nhds 0) := by sorry
