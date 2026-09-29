-- Prove2me | solution 1 for exists_contDiff_even_sub_comp_neg_eq_two_mul_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/56ff0e20-4c9e-5b43-a952-717cbe51a389

import Mathlib
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_contDiff_even_sub_comp_neg_eq_two_mul_smul

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (B : E × ℝ → F) (hB : ContDiff ℝ (⊤ : ℕ∞) B) :
    ∃ Q : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) Q ∧ (∀ (e : E) (ρ : ℝ), Q (e, -ρ) = Q (e, ρ)) ∧
      ∀ (e : E) (ρ : ℝ), B (e, ρ) - B (e, -ρ) = (2 * ρ) • Q (e, ρ) := by

  let dB : E × ℝ → F := fun p => fderiv ℝ B p ((0 : E), (1 : ℝ))
  have hdB : ContDiff ℝ (⊤ : ℕ∞) dB := (hB.fderiv_right (by exact_mod_cast le_top)).clm_apply contDiff_const
  let W : E × ℝ → F := fun p => dB p + dB (p.1, -p.2)
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := hdB.add (hdB.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hWev : ∀ (e : E) (r : ℝ), W (e, -r) = W (e, r) := by
    intro e r
    show dB (e, -r) + dB ((e, -r).1, -(e, -r).2) = dB (e, r) + dB ((e, r).1, -(e, r).2)
    simp only [neg_neg]
    exact add_comm _ _
  let I : E × ℝ → F := fun p => ∫ t in (0 : ℝ)..1, W (p.1, t * p.2)

  have hI : ContDiff ℝ (⊤ : ℕ∞) I := by
    rw [contDiff_iff_contDiffAt]
    intro p₀
    let χ : ContDiffBump p₀ := ⟨1, 2, one_pos, one_lt_two⟩
    let χ₂ : ContDiffBump ((1 : ℝ) / 2) := ⟨1, 2, one_pos, one_lt_two⟩
    let Ψ : ℝ × (E × ℝ) → F := fun q => ((χ : E × ℝ → ℝ) q.2 * (χ₂ : ℝ → ℝ) q.1) • W (q.2.1, q.1 * q.2.2)
    have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
      refine ContDiff.smul ((χ.contDiff.comp contDiff_snd).mul (χ₂.contDiff.comp contDiff_fst)) ?_
      exact hW.comp ((contDiff_fst.comp contDiff_snd).prodMk (contDiff_fst.mul (contDiff_snd.comp contDiff_snd)))
    have hΨc : HasCompactSupport Ψ := by
      refine HasCompactSupport.intro (χ₂.hasCompactSupport.prod χ.hasCompactSupport) fun q hq => ?_
      simp only [Set.mem_prod, not_and_or] at hq
      show ((χ : E × ℝ → ℝ) q.2 * (χ₂ : ℝ → ℝ) q.1) • W (q.2.1, q.1 * q.2.2) = 0
      rcases hq with h | h
      · rw [image_eq_zero_of_notMem_tsupport h, mul_zero, zero_smul]
      · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, zero_smul]
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 1)
    haveI : IsFiniteMeasureOnCompacts μ := inferInstance
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => ∫ t, (χ₂ : ℝ → ℝ) t • Ψ (id t, p) ∂μ) :=
      MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport μ id continuous_id
        (χ₂ : ℝ → ℝ) χ₂.continuous χ₂.hasCompactSupport Ψ hΨ hΨc
    have h12 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (χ₂ : ℝ → ℝ) t = 1 := by
      intro t ht
      refine χ₂.one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, Real.dist_eq]
      show |t - 1 / 2| ≤ 1
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hGI : ∀ p : E × ℝ, (∫ t, (χ₂ : ℝ → ℝ) t • Ψ (id t, p) ∂μ) = (χ : E × ℝ → ℝ) p • I p := by
      intro p
      show (∫ t in Set.Icc (0 : ℝ) 1, (χ₂ : ℝ → ℝ) t • Ψ (t, p)) = (χ : E × ℝ → ℝ) p • ∫ t in (0 : ℝ)..1, W (p.1, t * p.2)
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc, ← integral_smul]
      refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
      show (χ₂ : ℝ → ℝ) t • (((χ : E × ℝ → ℝ) p * (χ₂ : ℝ → ℝ) t) • W (p.1, t * p.2)) = (χ : E × ℝ → ℝ) p • W (p.1, t * p.2)
      rw [h12 t ht, one_smul, mul_one]
    have hev : I =ᶠ[𝓝 p₀] fun p : E × ℝ => ∫ t, (χ₂ : ℝ → ℝ) t • Ψ (id t, p) ∂μ := by
      filter_upwards [Metric.closedBall_mem_nhds p₀ one_pos] with p hp
      rw [hGI p, χ.one_of_mem_closedBall hp, one_smul]
    exact hG.contDiffAt.congr_of_eventuallyEq hev
  refine ⟨fun p => ((1 : ℝ) / 2) • I p, contDiff_const.smul hI, ?_, ?_⟩
  · intro e ρ
    show ((1 : ℝ) / 2) • (∫ t in (0 : ℝ)..1, W ((e, -ρ).1, t * (e, -ρ).2)) =
      ((1 : ℝ) / 2) • ∫ t in (0 : ℝ)..1, W ((e, ρ).1, t * (e, ρ).2)
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    show W (e, t * -ρ) = W (e, t * ρ)
    rw [mul_neg, hWev]
  · intro e ρ

    have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => B (e, r) - B (e, -r)) (W (e, r)) r := by
      intro r
      have h1 : HasDerivAt (fun r : ℝ => B (e, r)) (dB (e, r)) r := by
        have hc : HasDerivAt (fun r : ℝ => ((e, r) : E × ℝ)) ((0 : E), (1 : ℝ)) r :=
          (hasDerivAt_const r e).prodMk (hasDerivAt_id r)
        have := ((hB.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt r hc
        exact this
      have h2 : HasDerivAt (fun r : ℝ => B (e, -r)) (-dB (e, -r)) r := by
        have hc : HasDerivAt (fun r : ℝ => ((e, -r) : E × ℝ)) ((0 : E), (-1 : ℝ)) r :=
          (hasDerivAt_const r e).prodMk (hasDerivAt_neg r)
        have := ((hB.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt r hc
        have hneg : fderiv ℝ B (e, -r) ((0 : E), (-1 : ℝ)) = -dB (e, -r) := by
          rw [show (((0 : E), (-1 : ℝ)) : E × ℝ) = -((0 : E), (1 : ℝ)) by simp, map_neg]
        rw [← hneg]
        exact this
      have := h1.sub h2
      simp [W, sub_neg_eq_add] at this
      exact this
    have hFTC : ∫ r in (0 : ℝ)..ρ, W (e, r) = B (e, ρ) - B (e, -ρ) := by
      have hcont : Continuous fun r : ℝ => W (e, r) := hW.continuous.comp (continuous_const.prodMk continuous_id)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r) (hcont.intervalIntegrable _ _)]
      simp
    by_cases hρ : ρ = 0
    · subst hρ; simp
    · have hsub : ∫ t in (0 : ℝ)..1, W (e, t * ρ) = ρ⁻¹ • ∫ r in (0 : ℝ)..ρ, W (e, r) := by
        have := intervalIntegral.integral_comp_mul_right (f := fun r : ℝ => W (e, r)) (a := 0) (b := 1) hρ
        simpa using this
      show B (e, ρ) - B (e, -ρ) = (2 * ρ) • (((1 : ℝ) / 2) • ∫ t in (0 : ℝ)..1, W ((e, ρ).1, t * (e, ρ).2))
      rw [show (fun t : ℝ => W ((e, ρ).1, t * (e, ρ).2)) = fun t => W (e, t * ρ) from rfl, hsub, hFTC, smul_smul, smul_smul]
      rw [show (2 * ρ) * (1 / 2) * ρ⁻¹ = 1 by field_simp, one_smul]

end S_exists_contDiff_even_sub_comp_neg_eq_two_mul_smul
end P2MW
export P2MW.S_exists_contDiff_even_sub_comp_neg_eq_two_mul_smul (solution)
