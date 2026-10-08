-- Prove2me | Theorems.Thm_CappeKLUCB_Empirical_kinf_pos_finite
-- name    : CappeKLUCB.Empirical.kinf_pos_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:08:39.690266+00:00
-- url     : https://prove2.me/theorems/f8398ac9-aee8-452a-892c-8e2af26a9dd8
-- title:
--   §5, pp. 15–16, implicit in Theorem 2 — 0 < 𝒦_inf(ν, μ) < ∞ for ν ∈ ℱ and E(ν) < μ < 1
-- statement:
--   Let $\nu$ be a finitely supported probability distribution over $[0,1]$ and let $\mu$ satisfy $\mathrm E(\nu)<\mu<1$. Then
--   $$0<\mathcal K_{\inf}(\nu,\mu)<+\infty,$$
--   where $\mathcal K_{\inf}(\nu,\mu) = \inf\{\mathrm{KL}(\nu,\nu') : \nu'\in\mathcal F,\ \mathrm E(\nu')>\mu\}$ and $\mathcal F$ is the set of finitely supported probability distributions over $[0,1]$.
--
--   Applied to $\nu=\nu_a$ and $\mu=\mu^\star$ for a suboptimal arm $a$ under the hypothesis $\mu^\star<1$ of Theorem 2, this says that the quantities $\log(T)/\mathcal K_{\inf}(\nu_a,\mu^\star)$ and $\mathcal K_{\inf}(\nu_a,\mu^\star)^{-2}$ appearing in Theorem 2 are finite positive real numbers, so the bound is meaningful.
--
--   **Formalization Note** $\mathcal K_{\inf}$ is valued in $[0,+\infty]$. The paper does not state this fact separately; it is used implicitly in Theorem 2.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, pp. 15–16, Theorem 2 (implicit), with 𝒦_inf of (2), p. 3, for 𝒟 = ℱ

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

namespace CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

/-- `0 < 𝒦_inf(ν_a, μ⋆) < +∞`, implicit in Theorem 2 of Cappé et al., arXiv:1210.1136v4, §5,
pp. 15–16: for `ν ∈ ℱ` with `E(ν) < μ < 1`, the minimal divergence `𝒦_inf(ν, μ)` (model `ℱ`)
is positive and finite. -/
theorem kinf_pos_finite (ν : Measure ℝ) (hν : IsFinSupp01 ν) (μ : ℝ) (hlt : mean ν < μ)
    (hlt1 : μ < 1) :
    0 < Kinf ν μ ∧ Kinf ν μ < ⊤ := by sorry

end CappeKLUCB.Empirical
