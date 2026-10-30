-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_nonroot_above_phi_descending_scaled
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_original_nonroot_above_phi_descending_scaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:29:44.668982+00:00
-- url     : https://prove2.me/theorems/f716346d-531e-4be5-8976-a42ca4df6e14
-- title:
--   Original-clock descending Wiener–Hopf factor on the full shifted positive nonroot domain
-- statement:
--   For the original spectrally negative Lévy law with actual product exponential clock Exp(p+q), positive Esscher root φ and shifted λ>0, the source-specific descending transform has its exact cross-multiplied finite-scalar rational factor for every β>φ excluding the removable point β=φ+λ. This includes the previously untreated intermediate interval φ<β<φ+λ as well as β>φ+λ, with genuine time-dependent Esscher density and no global path-clock product assumption.
-- source:
--   Generalises the accepted above-root proof 02e15cf7 by directly reusing the same accepted source-specific all-real inverse Esscher drawdown factor 5f48ee29, actual tilted supremum moment 1a8d4fdc and full all-positive tilted descending factor e4e12a00. The only new domain restriction is the mathematically necessary shifted root disequality for the non-removable quotient.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_original_nonroot_above_phi_descending_scaled
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam m β : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hβ : φ < β) (hβne : β ≠ φ + lam)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    ENNReal.ofReal (φ + lam) *
      (ENNReal.ofReal p *
        (∫⁻ z : Ω × ℝ,
          ENNReal.ofReal (Real.exp
            (-β * (runningSup X (Real.toNNReal z.2) z.1 -
              X.X (Real.toNNReal z.2) z.1)))
          ∂(P.prod (expMeasure (p + q))))) =
    ENNReal.ofReal (p + q) *
      (ENNReal.ofReal lam *
        ENNReal.ofReal
          ((p / lam) *
            ((φ + lam - β) / (p + q - X.ψ β)))) := by sorry
