-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_prop_3_5_representation
-- name    : BenchmarkTracking.Verification.prop_3_5_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:05.63805+00:00
-- url     : https://prove2.me/theorems/e89f5d4c-f5cb-4b93-90e8-07613f431392
-- title:
--   Proposition 3.5 (second part) — bounded classical solutions of (3.38) have the representation (3.39)
-- statement:
--   Let the model parameters satisfy the standing assumptions and let $\rho>0$. Suppose $\psi$ is a classical solution of the Neumann problem (3.38) on $\mathbb R^2_+$ which is bounded: $|\psi(r,h)|\le C$ for some constant $C$ and all $(r,h)\in\mathbb R^2_+$. Then, on any probability space carrying three independent standard Brownian motions, for every $(r,h)\in\mathbb R^2_+$ the expectation below is finite and
--   $$
--   \psi(r,h)=-\beta\,\mathbb E\Big[\int_0^\infty e^{-\rho s-R^r_s}dK^h_s\Big],
--   $$
--   where $K^h$ is the local time of the reflected process $H^h$ at $0$, (3.5).
--
--   Together with the first part, this identifies the last term of $v$ in (3.1) with $\psi=\varphi+\xi$, which is what makes $v$ a classical solution in Theorem 3.1.
--
--   **Formalization Note** The paper's constant $C$ "depending on $(\mu,\sigma,\mu_B,\sigma_B,\gamma)$" only describes the constant; any bound $C$ is allowed here.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, p. 16, Proposition 3.5 (3.39)

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_PDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

theorem prop_3_5_representation {d : ℕ} (M : Params d) (hM : M.Standing) (ρ : ℝ) (hρ0 : 0 < ρ)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : EthierKurtz.IsStandardBrownian Pr B)
    (ψ : ℝ → ℝ → ℝ) (hψ : IsClassicalSol338 M ρ ψ)
    (hbdd : ∃ C : ℝ, ∀ r h : ℝ, 0 ≤ r → 0 ≤ h → |ψ r h| ≤ C) :
    ∀ r h : ℝ, 0 ≤ r → 0 ≤ h →
      expect3 M ρ Pr B r h < ∞ ∧ ψ r h = -M.beta * (expect3 M ρ Pr B r h).toReal := by sorry

end BenchmarkTracking.Verification
