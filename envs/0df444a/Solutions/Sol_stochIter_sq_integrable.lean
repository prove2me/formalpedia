-- Prove2me | solution 1 for stochIter_sq_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T18:04:28.651596+00:00
-- url     : https://prove2.me/submissions/d8c53985-e07b-4aba-a171-00606c7d631c

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology
open scoped InnerProductSpace
open ShorNonsmooth.Stochastic

theorem solution {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n))
    (xstar : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (B : ℝ) (hh_pos : ∀ y, 0 < h k y) (hh_bdd : ∀ y, h k y ≤ B)
    (hG_int : Integrable (G k) μ)
    (hG_sq_int : Integrable (fun ω => ‖G k ω‖ ^ 2) μ)
    (hx_int : Integrable (fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2) μ)
    (hx_meas : Measurable[(ℱ k : MeasurableSpace Ω)] (stochIter h G x₀ k)) :
    Integrable (fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2) μ := by
  have hstep : ∀ ω, stochIter h G x₀ (k + 1) ω
      = stochIter h G x₀ k ω - h k (stochIter h G x₀ k ω) • G k ω := by
    intro ω; simp [stochIter]
  have hsub : ∀ ω, stochIter h G x₀ (k + 1) ω - xstar
      = (stochIter h G x₀ k ω - xstar) - h k (stochIter h G x₀ k ω) • G k ω := by
    intro ω; rw [hstep ω]; abel
  have hsub' : ∀ ω, stochIter h G x₀ (Nat.succ k) ω - xstar
      = (stochIter h G x₀ k ω - xstar) - h k (stochIter h G x₀ k ω) • G k ω := by
    intro ω
    have : stochIter h G x₀ (Nat.succ k) ω = stochIter h G x₀ (k + 1) ω := rfl
    rw [this]
    exact hsub ω
  have hxk' : Measurable[m0] (stochIter h G x₀ k) :=
    Measurable.mono hx_meas (ℱ.le k)
      (@le_refl (MeasurableSpace (EuclideanSpace ℝ (Fin n)))
        (MeasurableSpace.instPartialOrder (α := EuclideanSpace ℝ (Fin n))).toPreorder _)
  have hB_nonneg : 0 ≤ B := by
    have h1 := hh_pos x₀
    have h2 := hh_bdd x₀
    linarith
  have hstepnorm : ∀ ω, ‖h k (stochIter h G x₀ k ω) • G k ω‖ ≤ B * ‖G k ω‖ := by
    intro ω
    have h1 : ‖h k (stochIter h G x₀ k ω) • G k ω‖
        = ‖h k (stochIter h G x₀ k ω)‖ * ‖G k ω‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hh_pos _))]
    have h2 : ‖h k (stochIter h G x₀ k ω)‖ ≤ B := by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hh_pos _))]
      exact hh_bdd _
    rw [h1]; exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have htri : ∀ ω, ‖stochIter h G x₀ (k + 1) ω - xstar‖
      ≤ ‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖ := by
    intro ω
    rw [hsub ω]
    calc ‖(stochIter h G x₀ k ω - xstar) - (h k (stochIter h G x₀ k ω) • G k ω)‖
        ≤ ‖stochIter h G x₀ k ω - xstar‖
            + ‖h k (stochIter h G x₀ k ω) • G k ω‖ := norm_sub_le _ _
      _ ≤ ‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖ := by
        have h4 := hstepnorm ω
        linarith
  -- The scalar estimate, on abstract reals only.
  have hscalar : ∀ a b B : ℝ, 0 ≤ B →
      (a + B * b) ^ 2 ≤ (1 + B) * (a ^ 2) + (B + B ^ 2) * (b ^ 2) := by
    intro a b B hB
    have hAM : 2 * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    have hexp : (a + B * b) ^ 2 = a ^ 2 + 2 * B * (a * b) + (B ^ 2) * (b ^ 2) := by ring
    rw [hexp]; nlinarith [hAM, hB]
  have hA_int : Integrable (fun ω => (1 + B) * (‖stochIter h G x₀ k ω - xstar‖ ^ 2)) μ :=
    hx_int.const_mul (1 + B)
  have hQ_int : Integrable (fun ω => (B + B ^ 2) * (‖G k ω‖ ^ 2)) μ :=
    hG_sq_int.const_mul (B + B ^ 2)
  have hsq_ae : AEStronglyMeasurable
      (fun ω => (‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖) ^ 2) μ := by
    have hxk_ae : AEStronglyMeasurable (fun ω => stochIter h G x₀ k ω) μ :=
      Measurable.aestronglyMeasurable hxk'
    have h1 : AEStronglyMeasurable (fun ω => ‖stochIter h G x₀ k ω - xstar‖) μ :=
      hxk_ae.sub (Measurable.aestronglyMeasurable measurable_const) |>.norm
    have hG_ae : AEStronglyMeasurable (fun ω => G k ω) μ := hG_int.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun ω => B * ‖G k ω‖) μ := hG_ae.norm.const_mul B
    have h3 : AEStronglyMeasurable
        (fun ω => ‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖) μ := h1.add h2
    exact h3.pow 2
  have hsq_int : Integrable (fun ω => (‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖) ^ 2) μ := by
    refine Integrable.mono (hA_int.add hQ_int) hsq_ae ?_
    filter_upwards with ω
    show ‖(‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖) ^ 2‖
      ≤ ‖(1 + B) * (‖stochIter h G x₀ k ω - xstar‖ ^ 2)
        + (B + B ^ 2) * (‖G k ω‖ ^ 2)‖
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg
      (mul_nonneg (show 0 ≤ 1 + B by linarith) (sq_nonneg _))
      (mul_nonneg (show 0 ≤ B + B ^ 2 by nlinarith [hB_nonneg]) (sq_nonneg _)))]
    exact hscalar _ _ _ hB_nonneg
  have hnext_ae : AEStronglyMeasurable (fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2) μ := by
    have hxk_ae : AEStronglyMeasurable (fun ω => stochIter h G x₀ k ω) μ :=
      Measurable.aestronglyMeasurable hxk'
    have hH_ae : AEStronglyMeasurable (fun ω => h k (stochIter h G x₀ k ω)) μ :=
      Measurable.aestronglyMeasurable ((hh_meas k).comp hxk')
    have hG_ae : AEStronglyMeasurable (fun ω => G k ω) μ := hG_int.aestronglyMeasurable
    have hstep_ae : AEStronglyMeasurable
        (fun ω => h k (stochIter h G x₀ k ω) • G k ω) μ := hH_ae.smul hG_ae
    have hdx_ae : AEStronglyMeasurable (fun ω => stochIter h G x₀ k ω - xstar) μ :=
      hxk_ae.sub (Measurable.aestronglyMeasurable measurable_const)
    have hdiff_ae : AEStronglyMeasurable
        (fun ω => (stochIter h G x₀ k ω - xstar) - h k (stochIter h G x₀ k ω) • G k ω) μ :=
      hdx_ae.sub hstep_ae
    have hn : AEStronglyMeasurable
        (fun ω => ‖(stochIter h G x₀ k ω - xstar) - h k (stochIter h G x₀ k ω) • G k ω‖) μ :=
      hdiff_ae.norm
    have hsq : AEStronglyMeasurable
        (fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2) μ := by
      have heq : (fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2)
          = (fun ω => ‖(stochIter h G x₀ k ω - xstar)
              - h k (stochIter h G x₀ k ω) • G k ω‖ ^ 2) := by
        funext ω
        show ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2
          = ‖(stochIter h G x₀ k ω - xstar)
              - h k (stochIter h G x₀ k ω) • G k ω‖ ^ 2
        rw [hsub ω]
      rw [heq]
      exact hn.pow 2
    exact hsq
  refine Integrable.mono hsq_int hnext_ae ?_
  filter_upwards with ω
  show ‖‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2‖
    ≤ ‖(‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖) ^ 2‖
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsq : (‖stochIter h G x₀ (k + 1) ω - xstar‖) ^ 2
      ≤ (‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖) ^ 2 := by
    have ha : 0 ≤ ‖stochIter h G x₀ (k + 1) ω - xstar‖ := norm_nonneg _
    have hb : 0 ≤ ‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖ :=
      add_nonneg (norm_nonneg _) (mul_nonneg hB_nonneg (norm_nonneg _))
    have htri' := htri ω
    nlinarith [sq_nonneg (‖stochIter h G x₀ k ω - xstar‖ + B * ‖G k ω‖
      - ‖stochIter h G x₀ (k + 1) ω - xstar‖)]
  exact hsq
