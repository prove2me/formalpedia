-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_tangential_hessian_positive
-- name    : BirkhoffGlobalSection.eh_left_tangential_hessian_positive
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-01T17:59:46.937501+00:00
-- url     : https://prove2.me/theorems/8bd5f4f6-2b5c-4e98-b13e-d2becd36fe64
-- title:
--   Positive tangential Hessian on the subcritical left EH component
-- statement:
--   Fix $c_0 > 2$. There are $\varepsilon, \eta > 0$ such that for every mass ratio and energy with
--
--   $$0 < \mu < 1, \qquad |\mu - 1/2| < \varepsilon, \qquad |c - c_0| < \eta, \qquad -c < h_1(\mu),$$
--
--   the centered-left elliptic-hyperbolic Hamiltonian $G_{\mu,c}$ has strictly positive tangential Hessian at every point of its selected zero-level component $\Sigma^{\mathrm{EH}}_{\mu,c}$:
--
--   $$DG_{\mu,c}(y)\,v = 0,\ v \ne 0 \quad\Longrightarrow\quad D^2 G_{\mu,c}(y)[v,v] > 0 \qquad (y \in \Sigma^{\mathrm{EH}}_{\mu,c}).$$
--
--   Here $\mu$ is the mass ratio, $c = -h$ is the Jacobi energy parameter, $-c < h_1(\mu)$ says the energy lies below the first critical value, and the component is the connected component of $\{G_{\mu,c} = 0\}$ through the designated left collision point.
--
--   This is the analytic half of the local subcritical convexity theorem: it certifies the strict convexity of the energy boundary through the second-derivative test, while existence of the compact convex body it bounds is a separate obligation.
--
--   **Formalization Note** The statement adapts the parameter neighborhood of Theorem 1.12 to the centered-left component; the hypothesis $c_0 > 2$ excludes the singular critical surface. Positivity is asserted on the component itself, so it transfers to any provably equal boundary.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS3, Theorem 9.4(ii) and Section 9.4 (completion of Theorem 1.12); https://arxiv.org/html/2506.17867v2#S10, paragraph constructing an open neighborhood of {1/2} x (-infinity,-2) on which both regularized components are strictly convex. Adapted to the centered-left explicit Hamiltonian and designated component; this child is the tangential-Hessian half.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.eh_left_tangential_hessian_positive
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c)
          (ehLeftEnergyComponent μ c) := by sorry
