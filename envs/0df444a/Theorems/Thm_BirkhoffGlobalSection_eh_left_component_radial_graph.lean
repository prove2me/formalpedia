-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_component_radial_graph
-- name    : BirkhoffGlobalSection.eh_left_component_radial_graph
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T08:20:16.347451+00:00
-- url     : https://prove2.me/theorems/79b813b7-a27f-46d4-8a82-b295ebfa5200
-- title:
--   Local subcritical EH component is a radial graph with negative interior
-- statement:
--   Fix $c_0>2$. There are $\varepsilon,\eta>0$ such that for every mass ratio and energy with
--
--   $$0<\mu<1,\qquad |\mu-1/2|<\varepsilon,\qquad |c-c_0|<\eta,\qquad -c<h_1(\mu),$$
--
--   the selected zero-level component $\Sigma^{\mathrm{EH}}_{\mu,c}$ of the centered-left elliptic-hyperbolic Hamiltonian $G_{\mu,c}$ is a radial graph over the round three-sphere, with $G_{\mu,c}$ negative inside. That is, for every unit vector $x\in S^3$:
--
--   - the ray $\{rx: r>0\}$ meets $\Sigma^{\mathrm{EH}}_{\mu,c}$;
--   - it meets it at exactly one scale $r>0$;
--   - if $Rx\in\Sigma^{\mathrm{EH}}_{\mu,c}$, then $G_{\mu,c}(rx)<0$ for $0\le r<R$.
--
--   Here $\mu$ is the mass ratio, $c=-h$ the Jacobi energy parameter, and $-c<h_1(\mu)$ says the energy lies below the first critical value.
--
--   This is the star-shapedness half of the local strict convexity in Liu--Salomão, Theorem 9.4(ii) and Section 9.4. The component bounds a strictly convex domain containing the origin, where $G_{\mu,c}(0)=-(1-\mu)<0$. Together with `eh_left_component_regular_compact_starshaped`, `eh_left_tangential_hessian_positive` and `convex_body_of_star_shaped_level_set`, it gives `eh_left_convex_body`. It replaces the disproved leaf `convex_body_of_regular_starshaped_hessian` in that branch.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S9.SS3, Theorem 9.4(ii) and Section 9.4 (completion of Theorem 1.12); https://arxiv.org/html/2506.17867v2#S10 (open neighborhood of {1/2} x (-infinity,-2) where both regularized components are strictly convex). Same parameter window as eh_left_component_regular_compact_starshaped.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- Near equal mass and near a fixed subcritical `c₀ > 2`, the selected elliptic-hyperbolic
component is a radial graph over the round three-sphere: every ray from the origin meets it,
at a unique positive scale, and the EH Hamiltonian is negative strictly before the hit. -/
theorem eh_left_component_radial_graph (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        (∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧
          (fun i : Fin 4 => r * x i) ∈ ehLeftEnergyComponent μ c) ∧
        (∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
          (fun i : Fin 4 => r * x i) ∈ ehLeftEnergyComponent μ c →
          (fun i : Fin 4 => t * x i) ∈ ehLeftEnergyComponent μ c → r = t) ∧
        (∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R →
          (fun i : Fin 4 => R * x i) ∈ ehLeftEnergyComponent μ c →
          ∀ r : ℝ, 0 ≤ r → r < R → ehLeftHamiltonian μ c (fun i : Fin 4 => r * x i) < 0) := by sorry

end BirkhoffGlobalSection
