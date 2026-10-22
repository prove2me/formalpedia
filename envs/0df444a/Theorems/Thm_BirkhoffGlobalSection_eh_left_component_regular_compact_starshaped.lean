-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_component_regular_compact_starshaped
-- name    : BirkhoffGlobalSection.eh_left_component_regular_compact_starshaped
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-01T19:07:07.587388+00:00
-- url     : https://prove2.me/theorems/08507c0a-bc35-4074-a8fa-36a98fba6bcc
-- title:
--   Regularity, compactness and star-shapedness of the left EH component
-- statement:
--   Fix $c_0 > 2$. There are $\varepsilon, \eta > 0$ such that for every mass ratio and energy with
--
--   $$0 < \mu < 1, \qquad |\mu - 1/2| < \varepsilon, \qquad |c - c_0| < \eta, \qquad -c < h_1(\mu),$$
--
--   the selected zero-level component $\Sigma^{\mathrm{EH}}_{\mu,c}$ of the centered-left elliptic-hyperbolic Hamiltonian $G_{\mu,c}$ is compact, the Hamiltonian is regular along it, and it is transverse to radial rays:
--
--   $$dG_{\mu,c}(y) \ne 0, \qquad dG_{\mu,c}(y)\,y > 0 \qquad (y \in \Sigma^{\mathrm{EH}}_{\mu,c}).$$
--
--   Here $\mu$ is the mass ratio, $c = -h$ is the Jacobi energy parameter, $-c < h_1(\mu)$ says the energy lies below the first critical value, and the component is the connected component of $\{G_{\mu,c} = 0\}$ through the designated left collision point. The radial inequality says the component meets every ray from the origin transversely, leaving the sub-level set toward increasing $G_{\mu,c}$.
--
--   This is the regularity-side estimate package behind the local subcritical convexity theorem: compactness plus transversality present the component as a radial graph over the sphere, while the Hessian positivity and the passage from estimates to a convex body are separate obligations.
--
--   **Formalization Note** The statement adapts the estimates of Theorem 9.4(ii) and Section 9.4 to the centered-left component; the hypothesis $c_0 > 2$ excludes the singular critical surface. No convexity or Hessian claim is made here.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS3, Theorem 9.4(ii) and Section 9.4 (completion of Theorem 1.12); https://arxiv.org/html/2506.17867v2#S10, paragraph constructing an open neighborhood of {1/2} x (-infinity,-2) on which both regularized components are strictly convex. Adapted to the centered-left explicit Hamiltonian and designated component; this child is the regularity-side estimate half.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.eh_left_component_regular_compact_starshaped
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        IsCompact (ehLeftEnergyComponent μ c) ∧
        (∀ y ∈ ehLeftEnergyComponent μ c,
          fderiv ℝ (ehLeftHamiltonian μ c) y ≠ 0) ∧
        (∀ y ∈ ehLeftEnergyComponent μ c,
          0 < fderiv ℝ (ehLeftHamiltonian μ c) y y) := by sorry
