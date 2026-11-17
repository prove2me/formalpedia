-- Prove2me | solution 1 for thm_7_5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:17:24.942759+00:00
-- url     : https://prove2.me/submissions/1bd7867b-68ea-454e-9c63-d36f1f1d3e5c

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic


/-

 # L1 convergence
The condition in DCT implies L1 convergence

-/

/-
\begin{thmbox}{7.5 ($L^1$ Convergence)}
With the conditions in Theorem 7.4, we have
\[
\int |X_n-X|\, d\mu \to 0, \qquad \text{as } n\to\infty.
\]
\end{thmbox}
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hXm : ∀ n, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (nhds (X ω))) :
    Tendsto (fun n => ∫ ω, ‖Xn n ω - X ω‖ ∂μ) atTop (nhds 0) := by

  have hX_meas : AEStronglyMeasurable X μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hXm h_lim

  have h_bound_all : ∀ᵐ ω ∂μ, ∀ n, ‖Xn n ω‖ ≤ Y ω :=
    eventually_countable_forall.2 h_bound

  have hX_bound : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ Y ω := by
    filter_upwards [h_bound_all, h_lim] with ω hω_bound hω_lim
    have hnorm_tendsto : Tendsto (fun n => ‖Xn n ω‖) atTop (nhds ‖X ω‖) :=
      (continuous_norm.tendsto (X ω)).comp hω_lim
    have hmem : ∀ᶠ n in atTop, ‖Xn n ω‖ ∈ Set.Iic (Y ω) :=
      Filter.Eventually.of_forall fun n => hω_bound n
    have hlimit_mem : ‖X ω‖ ∈ Set.Iic (Y ω) :=
      IsClosed.mem_of_tendsto isClosed_Iic hnorm_tendsto hmem
    simpa [Set.mem_Iic] using hlimit_mem

  have h_meas_diff : ∀ n, AEStronglyMeasurable (fun ω => ‖Xn n ω - X ω‖) μ := by
    intro n
    exact ((hXm n).sub hX_meas).norm

  have h_bound_diff : ∀ n, ∀ᵐ ω ∂μ, ‖‖Xn n ω - X ω‖‖ ≤ (2 : ℝ) * Y ω := by
    intro n
    filter_upwards [h_bound n, hX_bound] with ω hXn_le hX_le
    calc
      ‖‖Xn n ω - X ω‖‖ = ‖Xn n ω - X ω‖ := by simp
      _ ≤ ‖Xn n ω‖ + ‖X ω‖ := norm_sub_le _ _
      _ ≤ Y ω + Y ω := add_le_add hXn_le hX_le
      _ = (2 : ℝ) * Y ω := by ring

  have h_lim_diff : ∀ᵐ ω ∂μ, Tendsto (fun n => ‖Xn n ω - X ω‖) atTop (nhds 0) := by
    filter_upwards [h_lim] with ω hω_lim
    have hconst : Tendsto (fun _ : ℕ => X ω) atTop (nhds (X ω)) :=
      tendsto_const_nhds
    have hsub : Tendsto (fun n => Xn n ω - X ω) atTop (nhds (0 : ℝ)) := by
      simpa using hω_lim.sub hconst
    simpa [Function.comp_def] using (continuous_norm.tendsto (0 : ℝ)).comp hsub

  have h_twoY_int : Integrable (fun ω => (2 : ℝ) * Y ω) μ :=
    hYint.const_mul 2
  simpa using MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun ω => (2 : ℝ) * Y ω) h_meas_diff h_twoY_int h_bound_diff h_lim_diff