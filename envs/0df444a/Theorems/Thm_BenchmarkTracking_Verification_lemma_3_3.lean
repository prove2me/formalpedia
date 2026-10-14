-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_lemma_3_3
-- name    : BenchmarkTracking.Verification.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:04.276593+00:00
-- url     : https://prove2.me/theorems/1b2c752f-5de7-4c07-9487-961b0db467ca
-- title:
--   Lemma 3.3 — $G^h$ and $R^r$ are independent and $\varphi$ solves the Neumann problem (3.15)
-- statement:
--   Let the model parameters satisfy the standing assumptions, let $\rho>0$ and $\sigma_B\neq0$. On any probability space carrying three independent standard Brownian motions, let $\varphi(r,h)=-\beta\,\mathbb E[\int_0^\infty e^{-\rho s-R^r_s}dG^h_s]$ as in (3.13). Then:
--
--   1. for every $(r,h)\in\mathbb R^2_+$ the processes $G^h=(G^h_t)_{t\ge0}$ and $R^r=(R^r_t)_{t\ge0}$ are independent;
--   2. $\varphi$ is a classical solution of the Neumann problem
--   $$
--   \frac{\alpha^2}2\varphi_{rr}+\Big(\frac{\alpha^2}2-\rho\Big)\varphi_r+\frac{\sigma_B^2}2\varphi_{hh}-\mu_B\varphi_h=\rho\varphi\ \text{ on }(0,\infty)^2,\qquad \varphi_r(0,h)=0,\qquad \varphi_h(r,0)=\beta e^{-r}.
--   $$
--
--   This is the independent toy version of the last term of $v$; Proposition 3.5 reduces the correlated term to it.
--
--   **Formalization Note** The hypothesis $\sigma_B\neq0$ is not printed in Lemma 3.3; its proof uses $\varphi\in C^2$ from Lemma 3.4, which assumes it. $G^h$ is given by its explicit Skorokhod formula (p. 13). Independence is that of the two path-valued random variables. The uniqueness sentence "On the other hand, …" is not part of this statement.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, p. 10, Lemma 3.3 (3.13)–(3.15)

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_PDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

theorem lemma_3_3 {d : ℕ} (M : Params d) (hM : M.Standing) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hσB : M.sigmaB ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : EthierKurtz.IsStandardBrownian Pr B) :
    (∀ r h : ℝ, 0 ≤ r → 0 ≤ h →
      IndepFun (fun ω (t : ℝ) => regG M B h t ω) (fun ω (t : ℝ) => procR M ρ B r t ω) Pr) ∧
    IsClassicalSol315 M ρ (phiRep M ρ Pr B) := by sorry

end BenchmarkTracking.Verification
