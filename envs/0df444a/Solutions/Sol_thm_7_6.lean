-- Prove2me | solution 1 for thm_7_6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:38:06.007137+00:00
-- url     : https://prove2.me/submissions/9d3e19dc-9ef5-4e9c-a637-3dde0e9104f5

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic


/-

  # Theorem 7.6  DCT for complex functions in sequential form

-/

/-
\begin{thmbox}{7.6 (Complex DCT, Sequential Version)}
Let $X_n$ be complex-valued random variables, for $n=1,2,3,\dots$, defined on a measure space $(\Omega,\mathcal{F},\mu)$. Suppose $(X_n)_{n\ge 1}$ converges to $X$ almost everywhere for all $n$, and there exists an integrable function $Y$ such that $|X_n|\le Y$ almost everywhere for all $n$. Then $X\in L^1(\mu)$ and
\[
\lim_{n\to\infty} \int X_n\, d\mu = \int \lim_{n\to\infty} X_n\, d\mu.
\]
\end{thmbox}
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hXm : ∀ n, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) := by
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
  have hX_int : Integrable X μ :=
    Integrable.mono' hYint hX_meas hX_bound
  refine ⟨hX_int, ?_⟩
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    Y hXm hYint h_bound h_lim
