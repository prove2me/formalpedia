-- Prove2me | Theorems.Thm_DeepONetUniversal_tauber_wiener_iff_not_polynomial
-- name    : DeepONetUniversal.tauber_wiener_iff_not_polynomial
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:31:47.359365+00:00
-- url     : https://prove2.me/theorems/130468a5-8a52-42a6-9770-78e337cce096
-- title:
--   Theorem 3: sufficient condition for TW
-- statement:
--   Let $\sigma:\mathbb{R}\to\mathbb{R}$ be continuous and a tempered distribution, $\sigma\in S'(\mathbb{R})$. Then
--
--   $$\sigma\in(\mathrm{TW})\iff\sigma\text{ is not a polynomial},$$
--
--   that is, the linear combinations $\sum_{i=1}^Nc_i\sigma(\lambda_ix+\theta_i)$ are dense in every $C([a,b])$ if and only if $\sigma$ is not a polynomial.
--
--   This is the criterion that makes the usual activations (sigmoid, $\tanh$, ReLU) admissible in Theorems 4 and 5.
--
--   **Formalization Note** $\sigma\in S'(\mathbb{R})$ is stated as: there is a continuous linear functional $T$ on the Schwartz space with $T(\varphi)=\int\sigma\varphi$ for every compactly supported Schwartz function $\varphi$.
-- source:
--   Lu, Jin and Karniadakis, DeepONet: Learning nonlinear operators for identifying differential equations based on the universal approximation theorem of operators, arXiv:1910.03193v3 (2019), Appendix A, Theorem 3, p. 19

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology

namespace DeepONetUniversal

theorem tauber_wiener_iff_not_polynomial (σ : ℝ → ℝ) (hσc : Continuous σ)
    (hσt : IsTemperedDistribution σ) :
    IsTauberWiener σ ↔ ¬ IsPolynomialFun σ := by sorry

end DeepONetUniversal
