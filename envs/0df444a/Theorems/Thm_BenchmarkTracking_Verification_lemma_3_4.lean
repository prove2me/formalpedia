-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_lemma_3_4
-- name    : BenchmarkTracking.Verification.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:13.374514+00:00
-- url     : https://prove2.me/theorems/da1a13e9-5c5f-41a7-8cae-4b1d2f790ab2
-- title:
--   Lemma 3.4 — $\varphi\in C^{2,2}(\mathbb R^2_+)$ when $\sigma_B\neq0$
-- statement:
--   Let the model parameters satisfy the standing assumptions, let $\rho>0$, and assume $\sigma_B\neq0$. On any probability space carrying three independent standard Brownian motions, let
--   $$
--   \varphi(r,h)=-\beta\,\mathbb E\Big[\int_0^\infty e^{-\rho s-R^r_s}dG^h_s\Big],\qquad (r,h)\in\mathbb R^2_+,
--   $$
--   where $R^r$ is the reflected drifted Brownian motion (3.2) driven by $B^1$ and $G^h$ is the regulator of the reflected process $P^h_t=h-\mu_Bt-\sigma_BB^0_t+G^h_t$ (3.14), driven by $B^0$. Then the expectation is finite for every $(r,h)\in\mathbb R^2_+$ and
--   $$
--   \varphi\in C^2(\mathbb R^2_+),
--   $$
--   twice continuously differentiable on the closed quadrant up to the boundary.
--
--   This is the smoothness input for Lemma 3.3 and for the homogenization of Proposition 3.5, where $\varphi_{rh}$ enters the definition of $\xi$.
--
--   **Formalization Note** $C^{2,2}(\mathbb R^2_+)$ is read as `ContDiffOn ℝ 2` on $[0,\infty)^2$. The representations (3.16)–(3.18) of the derivatives are not part of this statement.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, p. 10, Lemma 3.4

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_PDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

theorem lemma_3_4 {d : ℕ} (M : Params d) (hM : M.Standing) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hσB : M.sigmaB ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : EthierKurtz.IsStandardBrownian Pr B) :
    (∀ r h : ℝ, 0 ≤ r → 0 ≤ h → expectG M ρ Pr B r h < ∞) ∧
    ContDiffOn ℝ 2 (fun q : ℝ × ℝ => phiRep M ρ Pr B q.1 q.2) (Ici 0 ×ˢ Ici 0) := by sorry

end BenchmarkTracking.Verification
