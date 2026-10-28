-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
-- name    : AvramDividend.Classical.avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T10:15:29.619189+00:00
-- url     : https://prove2.me/theorems/e4e12a00-3785-4af6-9fde-d20df7a0d7bd
-- title:
--   Genuine finite-rate random-terminal Esscher descending Wiener–Hopf transform at every positive beta
-- statement:
--   For the actual spectrally negative Lévy process, q>0, φ>0 with ψ(φ)=q, and any p>0, λ>0 with ψ(φ+λ)−q=p, the joint path/real-Exp(p) measure weighted at its actual observation time by exp(φX_e−eψ(φ)) has descending reflected drawdown D_e=S_e−X_e with Laplace transform (p/λ)(λ−β)/(p−(ψ(φ+β)−q)) for every β>0 distinct from λ. At β=λ it equals p/(λm), where m=ψ′(φ+λ)>0 is an explicit HasDerivAt hypothesis. The genuine joint-likelihood measurability is explicit. No independence, analytic extension, two-sided exit, or desired factor is assumed; those are proof obligations.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), §2.1 eqs. (2.4)–(2.7), §2.2 Corollary 2.2 and analytic extension; tilted exponent ψφ(β)=ψ(φ+β)−q. Actual random-terminal Esscher density and reflected-drawdown observable match Proved 146b0027 and 858282df. Distinct from coordinator scalar 07c7d8b4, which concerns p↓0. Publication repair: the original binder used reserved `λ` syntax; all formal occurrences now use `lam` with identical mathematical meaning.

import Mathlib
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_Reflection

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam m : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    ∀ β : ℝ, 0 < β →
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp
          (-β * (runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1)))
        ∂((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) =
      ENNReal.ofReal
        (if β = lam then p / (lam * m)
         else (p / lam) * ((lam - β) / (p - (X.ψ (φ + β) - q)))) := by sorry
