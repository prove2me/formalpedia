-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_convex_body
-- name    : BirkhoffGlobalSection.eh_left_convex_body
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-01T17:59:33.964698+00:00
-- url     : https://prove2.me/theorems/203f570a-7193-4337-884a-cf74f0446156
-- title:
--   Subcritical left EH component bounds a compact convex body
-- statement:
--   Fix $c_0 > 2$. There are $\varepsilon, \eta > 0$ such that for every mass ratio and energy with
--
--   $$0 < \mu < 1, \qquad |\mu - 1/2| < \varepsilon, \qquad |c - c_0| < \eta, \qquad -c < h_1(\mu),$$
--
--   the selected zero-level component $\Sigma^{\mathrm{EH}}_{\mu,c}$ of the centered-left elliptic-hyperbolic Hamiltonian $G_{\mu,c}$ is the boundary of a compact convex body:
--
--   $$B \subset \mathbb{R}^4 \text{ compact and convex}, \qquad 0 \in \mathrm{int}\, B, \qquad \partial B = \Sigma^{\mathrm{EH}}_{\mu,c}.$$
--
--   Here $\mu$ is the mass ratio ($\mu = 1/2$ is the equal-mass case), $c = -h$ is the Jacobi energy parameter, $-c < h_1(\mu)$ says the energy lies below the first critical value, and the component $\Sigma^{\mathrm{EH}}_{\mu,c}$ is the connected component of $\{G_{\mu,c} = 0\}$ through the designated left collision point.
--
--   This is the geometric half of the local subcritical convexity theorem: it provides the compact convex body whose boundary carries the regularized dynamics, while positivity of the tangential Hessian on that boundary is a separate obligation.
--
--   **Formalization Note** The statement adapts the parameter neighborhood of Theorem 1.12 to the centered-left component; the hypothesis $c_0 > 2$ excludes the singular critical surface. No regularity or Hessian claim is made here.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS3, Theorem 9.4(ii) and Section 9.4 (completion of Theorem 1.12); https://arxiv.org/html/2506.17867v2#S10, paragraph constructing an open neighborhood of {1/2} x (-infinity,-2) on which both regularized components are strictly convex. Adapted to the centered-left explicit Hamiltonian and designated component; this child is the convex-body half.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.eh_left_convex_body
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B := by sorry
