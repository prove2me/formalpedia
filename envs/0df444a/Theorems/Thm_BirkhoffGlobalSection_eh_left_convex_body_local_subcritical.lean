-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_convex_body_local_subcritical
-- name    : BirkhoffGlobalSection.eh_left_convex_body_local_subcritical
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-01T01:06:39.581717+00:00
-- url     : https://prove2.me/theorems/6b6bfa81-ba62-42a6-a9c1-13708e34a3fb
-- title:
--   Local convex body and positive tangential Hessian in centered elliptic-hyperbolic coordinates
-- statement:
--   Fix $c_0>2$. There are $\varepsilon,\eta>0$ such that, for
--
--   $$0<\mu<1,\qquad |\mu-1/2|<\varepsilon,\qquad |c-c_0|<\eta,\qquad -c<h_1(\mu),$$
--
--   the selected zero-level component $\Sigma^{\mathrm{EH}}_{\mu,c}$ of the explicit centered-left elliptic-hyperbolic Hamiltonian $G_{\mu,c}$ bounds a compact convex body $B\subset\mathbb R^4$ with
--
--   $$0\in\operatorname{int}B,\qquad \partial B=\Sigma^{\mathrm{EH}}_{\mu,c}.$$
--
--   The Hamiltonian is $C^2$ near every point of this boundary, and its tangential Hessian is strictly positive:
--
--   $$D G_{\mu,c}(y)v=0,\quad v\ne0\quad\Longrightarrow\quad D^2G_{\mu,c}(y)[v,v]>0\qquad(y\in\partial B).$$
--
--   This is the local geometric persistence step at a regular equal-mass energy. It concerns the explicit elliptic-hyperbolic component only; identification with the Levi-Civita component and compatibility of their clocks are separate obligations.
--
--   **Formalization Note.** The assertion adapts Theorem 1.12 and the open parameter neighborhood in Section 10 to the centered-left component defined by a specified collision point. The hypothesis $c_0>2$ excludes the singular critical surface.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS3, Theorem 9.4(ii) and Section 9.4 (completion of Theorem 1.12); https://arxiv.org/html/2506.17867v2#S10, paragraph constructing an open neighborhood of {1/2} x (-infinity,-2) on which both regularized components are strictly convex. Adapted to the centered-left explicit Hamiltonian and designated component.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.eh_left_convex_body_local_subcritical
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B ∧
          HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c) (frontier B) := by sorry
