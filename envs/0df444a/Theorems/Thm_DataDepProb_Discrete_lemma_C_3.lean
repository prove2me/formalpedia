-- Prove2me | Theorems.Thm_DataDepProb_Discrete_lemma_C_3
-- name    : DataDepProb.Discrete.lemma_C_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:12:46.569944+00:00
-- url     : https://prove2.me/theorems/ee74ed0e-8ecc-4194-9807-0716071c08f5
-- title:
--   Lemma C.3 — reduction to a scalar equation: Lipschitz bounds for $p_\theta$, $\varphi$ and the unique zero of $\Psi$
-- statement:
--   Let $\eta>0$ and let $q^+=\mathrm{MW}_\eta(q,f,b)$, $e=e_s$ be the inputs of Appendix C. For $\theta,\theta'\ge0$,
--   $$\|p_\theta-p_{\theta'}\|_1^2\le(\theta'-\theta)\big(\varphi(\theta)-\varphi(\theta')\big).$$
--   Consequently, $\varphi$ is nonincreasing and $\|p_\theta-p_{\theta'}\|_1\le\Gamma|\theta-\theta'|$, $|\varphi(\theta)-\varphi(\theta')|\le\Gamma^2|\theta-\theta'|$. If $\lambda>0$, then $\Psi(\theta)=\theta-16\lambda\varphi(\theta)$ has a unique zero $\theta^*$ in $[0,\Theta]$, where $\Theta=16\lambda\log(1+d)$, and $p^*=p_{\theta^*}$.
--
--   The lemma reduces the coupled penalized projection to a one-dimensional root-finding problem, which Algorithm 4 solves by bisection.
--
--   Differences from the source:
--   - reading: the standing inputs of Appendix C → hypothesis `ProjInput η qplus e` ($e=e_s$, $n\ge1$; $q^+=\mathrm{MW}_\eta(q,f,b)$ with $q\in\tilde\Delta_d$, $f\in[0,1]^{[d]}$, $b=(f(y)+E_u[f])/2$); reason: Appendix C's section assumption.
--   - reading: "$\varphi$ is nonincreasing" → `AntitoneOn φ [0, ∞)`; reason: $\varphi$ is defined for $\theta\ge0$.
--   - reading: "$p^*=p_{\theta^*}$" with $p^*$ the minimizer of $A_s$ over $\tilde\Delta_d$ → every minimizer $p^*$ equals $p_{\theta^*}$ for the zero $\theta^*$; reason: $p^*$ is introduced in Lemma C.2 as "let $p^*$ minimize $A_s$".
--   - encoding: $p_\theta$ → `pTheta`, the minimizer selected by `Classical.epsilon`; reason: it exists and is unique for $\theta\ge0$.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 38, Lemma C.3 (proof p. 40)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_ScalarReduction

namespace DataDepProb.Discrete

/-- Lemma C.3 (reduction to a scalar equation, p. 38). Let `η > 0` and let `q⁺ = MW_η(q, f, b)`,
`e = e_s` be the inputs of Appendix C. For `θ, θ′ ≥ 0`,
`‖p_θ − p_θ′‖₁² ≤ (θ′ − θ)(φ(θ) − φ(θ′))`. Consequently `φ` is nonincreasing on `[0, ∞)`,
`‖p_θ − p_θ′‖₁ ≤ Γ|θ − θ′|` and `|φ(θ) − φ(θ′)| ≤ Γ²|θ − θ′|`. If `λ > 0`, then
`Ψ(θ) = θ − 16λφ(θ)` has a unique zero `θ*` in `[0, Θ]`, `Θ = 16λ log(1 + d)`, and the minimizer
`p*` of `A_s` over `∆̃_d` equals `p_θ*`. -/
theorem lemma_C_3 {d : ℕ} (η lam : ℝ) (hη : 0 < η) (qplus e : Fin d → ℝ)
    (hin : ProjInput η qplus e) :
    (∀ θ θ' : ℝ, 0 ≤ θ → 0 ≤ θ' →
      l1dist (pTheta qplus e θ) (pTheta qplus e θ') ^ 2 ≤
        (θ' - θ) * (phi qplus e θ - phi qplus e θ')) ∧
    AntitoneOn (phi qplus e) (Set.Ici 0) ∧
    (∀ θ θ' : ℝ, 0 ≤ θ → 0 ≤ θ' →
      l1dist (pTheta qplus e θ) (pTheta qplus e θ') ≤ gammaC d * |θ - θ'| ∧
      |phi qplus e θ - phi qplus e θ'| ≤ gammaC d ^ 2 * |θ - θ'|) ∧
    (0 < lam →
      (∃! θs : ℝ, θs ∈ Set.Icc 0 (ThetaC lam d) ∧ Psi lam qplus e θs = 0) ∧
      ∀ θs ∈ Set.Icc 0 (ThetaC lam d), Psi lam qplus e θs = 0 →
        ∀ pstar ∈ truncSimplex d, IsMinOn (objA lam qplus e) (truncSimplex d) pstar →
          pstar = pTheta qplus e θs) := by sorry

end DataDepProb.Discrete
