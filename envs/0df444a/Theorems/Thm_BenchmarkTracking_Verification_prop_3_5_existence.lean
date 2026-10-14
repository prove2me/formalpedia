-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_prop_3_5_existence
-- name    : BenchmarkTracking.Verification.prop_3_5_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:17.327006+00:00
-- url     : https://prove2.me/theorems/e8d5fa39-5039-4a7a-b0f7-32117a47e532
-- title:
--   Proposition 3.5 (first part) — $\psi=\varphi+\xi$ solves the Neumann problem (3.38)
-- statement:
--   Let the model parameters satisfy the standing assumptions, let $\rho>0$ and $\sigma_B\neq0$. On any probability space carrying three independent standard Brownian motions, for $(r,h)\in\mathbb R^2_+$ let
--   $$
--   \xi(r,h)=-\kappa_1\mathbb E\Big[\int_0^\infty e^{-\rho s}\varphi_{rh}(R^r_s,H^h_s)\,ds\Big],\qquad \psi(r,h)=\varphi(r,h)+\xi(r,h),
--   $$
--   with $\varphi$ of (3.13) and the reflected processes $R^r$, $H^h$ of (3.2), (3.3). Then:
--
--   1. for every $(r,h)\in\mathbb R^2_+$ the map $(\omega,s)\mapsto e^{-\rho s}\varphi_{rh}(R^r_s,H^h_s)$ is integrable with respect to $\mathbb P\otimes ds$ on $\Omega\times[0,\infty)$, so $\xi$ is well defined;
--   2. $\psi$ is a classical solution of
--   $$
--   \frac{\alpha^2}2\psi_{rr}+\Big(\frac{\alpha^2}2-\rho\Big)\psi_r+\frac{\sigma_B^2}2\psi_{hh}-\mu_B\psi_h-\kappa_1\psi_{rh}=\rho\psi\ \text{ on }(0,\infty)^2,\qquad \psi_r(0,h)=0,\qquad \psi_h(r,0)=\beta e^{-r}.
--   $$
--
--   This is the homogenization step: the correlated reflected pair $(R^r,H^h)$ is handled through the independent problem of Lemma 3.3 plus a problem with homogeneous Neumann conditions.
--
--   **Formalization Note** $\sigma_B\neq0$ is added: the proposition uses $\varphi\in C^2(\mathbb R^2_+)$, which is Lemma 3.4 under $\sigma_B\neq0$. The paper's "$\forall(r,h)\in\mathbb R_+$" in (3.37) is read as $\mathbb R^2_+$. The integrability conclusion makes the Bochner integrals in $\xi$ the true ones.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, p. 16, Proposition 3.5 (3.36)–(3.38)

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_PDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

theorem prop_3_5_existence {d : ℕ} (M : Params d) (hM : M.Standing) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hσB : M.sigmaB ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : EthierKurtz.IsStandardBrownian Pr B) :
    (∀ r h : ℝ, 0 ≤ r → 0 ≤ h →
      Integrable (fun q : Ω × ℝ => Real.exp (-ρ * q.2) *
          phiRH M ρ Pr B (procR M ρ B r q.2 q.1) (procH M B h q.2 q.1))
        (Pr.prod (volume.restrict (Ici 0)))) ∧
    IsClassicalSol338 M ρ (psiRep M ρ Pr B) := by sorry

end BenchmarkTracking.Verification
