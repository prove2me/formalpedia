-- Prove2me | Theorems.Thm_EntTensor_integral_prod_density_mul_log_eq_add
-- name    : EntTensor.integral_prod_density_mul_log_eq_add
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T03:59:19.194595+00:00
-- url     : https://prove2.me/theorems/79285590-5448-4480-a3f4-b7c01c68d8c3
-- title:
--   Tensorization of the entropy functional over a product density
-- statement:
--   Tensorization (sub-additivity) of the entropy functional for a product density. For probability measures $\mu, \nu$ and densities $g_1 \ge 0$ with $\int g_1\,d\mu = 1$ and $g_2 \ge 0$ with $\int g_2\,d\nu = 1$ (each with integrable entropy integrand $g_i \log g_i$), the entropy of the product density $(x,y)\mapsto g_1(x)\,g_2(y)$ over $\mu\otimes\nu$ splits as the sum of the per-factor entropies: $$\int (g_1\,g_2)\log(g_1\,g_2)\,d(\mu\otimes\nu) = \int g_1\log g_1\,d\mu + \int g_2\log g_2\,d\nu.$$ This is the entropy-functional level of the Kullback–Leibler tensorization (Han's inequality / sub-additivity of entropy, BLM Theorem 4.10) for independent coordinates: it is obtained by lifting the KL tensorization $\mathrm{KL}(\mu_1\otimes\mu_2\|\nu_1\otimes\nu_2)=\mathrm{KL}(\mu_1\|\nu_1)+\mathrm{KL}(\mu_2\|\nu_2)$ through the Ent–KL bridge identity. It is the product-density specialization of the sub-additivity step used in the entropy method (Herbst / modified log-Sobolev).
-- source:
--   Boucheron, Lugosi, Massart, *Concentration Inequalities*, OUP 2013, §4.1, Theorem 4.10 (sub-additivity / tensorization of entropy, derived from Han's inequality for relative entropies).

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Prod
open Real MeasureTheory InformationTheory
open scoped ENNReal NNReal

theorem EntTensor.integral_prod_density_mul_log_eq_add
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g₁ : α → ℝ} {g₂ : β → ℝ}
    (hg₁_meas : Measurable g₁) (hg₁_nonneg : ∀ x, 0 ≤ g₁ x)
    (hg₁_int : Integrable g₁ μ) (hg₁_mass : ∫ x, g₁ x ∂μ = 1)
    (hg₁_ent : Integrable (fun x ↦ g₁ x * log (g₁ x)) μ)
    (hg₂_meas : Measurable g₂) (hg₂_nonneg : ∀ y, 0 ≤ g₂ y)
    (hg₂_int : Integrable g₂ ν) (hg₂_mass : ∫ y, g₂ y ∂ν = 1)
    (hg₂_ent : Integrable (fun y ↦ g₂ y * log (g₂ y)) ν) :
    (∫ z, (g₁ z.1 * g₂ z.2) * log (g₁ z.1 * g₂ z.2) ∂(μ.prod ν))
      = (∫ x, g₁ x * log (g₁ x) ∂μ) + (∫ y, g₂ y * log (g₂ y) ∂ν) := by sorry
