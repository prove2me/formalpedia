-- Prove2me | solution 1 for neumann_certificate_remainder_small_with_explicit_formula
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T05:29:44.984785+00:00
-- url     : https://prove2.me/submissions/2eafc820-2710-4e7d-b7ce-d8ba4130c456

import Theorems.Thm_candes_recht_theorem42_tangent_sampling_deviation_bound_with_sample_constant
import Theorems.Thm_neumann_remainder_tangent_scale_le_half_from_sample_bound
import Theorems.Thm_neumann_certificate_remainder_bound_from_scaled_tangent_concentration
import Theorems.Thm_bernoulli_tangent_sampling_concentration_from_deviation_bound
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF pp. 20-21, Lemma 4.8, together with the
tangent-deviation estimate from PDF pp. 18-20, Theorem 4.2, equations
(4.9)--(4.10), and the scale-smallness choice in Lemma 4.8.

Prove Lemma 4.8 in explicit-formula form by applying the paper-level Theorem
4.2 formula-scale tangent-deviation bound, converting deviation control to
tangent concentration, choosing the Lemma 4.8 sample constant large enough that
the contraction scale is at most `1/2`, and then invoking the deterministic
Neumann-series tail estimate.  This avoids the legacy coefficient-1 dense
wrapper, whose statement is not the source-faithful place to discharge the
Appendix 9.1 `E Z ≤ 1` proviso. -/
theorem solution :
    ∃ CR Ctail ctail : ℝ, 0 < CR ∧ 0 < Ctail ∧ 0 < ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          CR * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTailSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 3
                (neumannRemainderFormulaBound Ctail β μ₀ (max n₁ n₂) r m)) ≥
          1 - ctail * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases candes_recht_theorem42_tangent_sampling_deviation_bound_with_sample_constant with
    ⟨Cdev, cdev, hCdev, hcdev, hDeviation⟩
  rcases neumann_remainder_tangent_scale_le_half_from_sample_bound Cdev with
    ⟨Cscale, hCscale, hScaleSmallFromSample⟩
  rcases neumann_certificate_remainder_bound_from_scaled_tangent_concentration Cdev with
    ⟨Ctail, hCtail, hTailFromConcentration⟩
  let CR : ℝ := max Cdev Cscale
  have hCR : 0 < CR := lt_of_lt_of_le hCdev (le_max_left Cdev Cscale)
  refine ⟨CR, Ctail, cdev, hCR, hCtail, hcdev, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  let n : ℕ := max n₁ n₂
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hn : 0 < n := by
    dsimp [n]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hn_real_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hβ_nonneg : 0 ≤ β := by linarith
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_real_ge_one
  have htail_nonneg :
      0 ≤ μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by
    positivity
  have hCdev_le_CR : Cdev ≤ CR := le_max_left Cdev Cscale
  have hCscale_le_CR : Cscale ≤ CR := le_max_right Cdev Cscale
  have hCdevLower :
      (m : ℝ) ≥ Cdev * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) := by
    have hle :
        Cdev * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) ≤
          CR * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hCdev_le_CR htail_nonneg
    calc
      Cdev * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ))
          = Cdev * (μ₀ * (n : ℝ) * (r : ℝ) *
              (β * Real.log (n : ℝ))) := by ring
      _ ≤ CR * (μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ))) := hle
      _ = CR * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) := by ring
      _ ≤ (m : ℝ) := by
        simpa [CR, n, mul_assoc] using hmLower
  have hCscaleLower :
      (m : ℝ) ≥ Cscale * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) := by
    have hle :
        Cscale * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) ≤
          CR * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hCscale_le_CR htail_nonneg
    calc
      Cscale * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ))
          = Cscale * (μ₀ * (n : ℝ) * (r : ℝ) *
              (β * Real.log (n : ℝ))) := by ring
      _ ≤ CR * (μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ))) := hle
      _ = CR * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) := by ring
      _ ≤ (m : ℝ) := by
        simpa [CR, n, mul_assoc] using hmLower
  have hScaleSmall :
      tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m ≤ (1 : ℝ) / 2 :=
    by
      simpa [n] using
        hScaleSmallFromSample β hβ n r m μ₀ hn hr hμ₀ hCscaleLower
  have hDeviationProb :
      bernoulliEventProb p
          (fun Omega =>
            TangentSamplingDeviationBound Omega S p
              (tangentSamplingDeviationScale Cdev β μ₀ n r m)) ≥
        1 - cdev * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [p, n] using
      hDeviation CR hCdev_le_CR β hβ n₁ n₂ r m M μ₀ S
        hn₁ hn₂ hr hm hμ₀ hA0 (by simpa [CR, n, mul_assoc] using hmLower)
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  have hConcentrationProb :
      bernoulliEventProb p
          (fun Omega =>
            TangentSamplingConcentration Omega S p
              (tangentSamplingDeviationScale Cdev β μ₀ n r m)) ≥
        1 - cdev * Real.rpow (↑(max n₁ n₂)) (-β) :=
    bernoulli_tangent_sampling_concentration_from_deviation_bound S p
      (tangentSamplingDeviationScale Cdev β μ₀ n r m) cdev β
      hpNonneg hpLeOne hDeviationProb
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            TangentSamplingConcentration Omega S p
              (tangentSamplingDeviationScale Cdev β μ₀ n r m)) ≤
        bernoulliEventProb p
          (fun Omega =>
            NeumannCertificateTailSpectralBound Omega S
              p 3 (neumannRemainderFormulaBound Ctail β μ₀ n r m)) :=
    bernoulli_event_probability_mono
      p
      (fun Omega =>
        TangentSamplingConcentration Omega S p
          (tangentSamplingDeviationScale Cdev β μ₀ n r m))
      (fun Omega =>
        NeumannCertificateTailSpectralBound Omega S
          p 3 (neumannRemainderFormulaBound Ctail β μ₀ n r m))
      hpNonneg hpLeOne
      (by
        intro Omega hOmegaConcentration
        simpa [p, n] using
          hTailFromConcentration β hβ n₁ n₂ r m M μ₀ μ₁ S Omega
            hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hScaleSmall
            (by simpa [p, n] using hOmegaConcentration))
  simpa [p, n] using le_trans hConcentrationProb hMono
