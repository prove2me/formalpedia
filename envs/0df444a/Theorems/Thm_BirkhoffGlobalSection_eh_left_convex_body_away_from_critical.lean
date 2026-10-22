-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_convex_body_away_from_critical
-- name    : BirkhoffGlobalSection.eh_left_convex_body_away_from_critical
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T14:58:21.688441+00:00
-- url     : https://prove2.me/theorems/791c1f4d-d81a-42b6-924d-47bbc38cff9d
-- title:
--   Uniform convex body of the EH component away from the critical energy
-- statement:
--   For every $\eta>0$ there is a mass radius $\varepsilon>0$, uniform in the energy, such that whenever
--
--   $$0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c\ge2+\eta,\qquad -c<h_1(\mu),$$
--
--   the selected centered-left EH component $\Sigma^{\mathrm{EH}}_{\mu,c}$ is the frontier of a compact convex body $B$ with $0\in\operatorname{int}B$, and $G_{\mu,c}$ has positive tangential Hessian on $\partial B$.
--
--   This is the uniform-in-energy form of `eh_left_convex_body_local_subcritical`.
--
--   **Intended proof.**
--   - **Rescaling.** Put $x=X/\sqrt c$ and $u=1/c$. The rescaled Hamiltonian $\tilde G_{\mu,u}(X,y)=G_{\mu,1/u}(\sqrt u\,X,y)$ extends continuously, with its first two derivatives, to $u=0$. There its zero level is the ellipsoid $\tfrac12|y|^2+\tfrac14|X|^2=1-\mu$.
--   - **Linear invariance.** The rescaling is linear, so convexity, star-shapedness and positivity of the tangential Hessian transfer.
--   - **Strict estimates.** At $\mu=\tfrac12$, $u\in(0,1/2)$ they are the Proved `eh_half_mass_star_shaped` and `eh_half_mass_tangential_hessian` (Liu--Salomão Theorem 9.4(ii)). At $u=0$ they are explicit.
--   - **Compactness.** The tube lemma of `BirkhoffGlobalSection_EHConvexPerturbation`, applied over the compact parameter set $\{\tfrac12\}\times[0,1/(2+\eta)]$, gives one mass radius. The radial-graph and convex-body steps then follow as in the local leaves (`convex_body_of_star_shaped_level_set`).
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS3 and #S10 (Theorem 9.4(ii); strict convexity on an open neighborhood of {1/2} x (-infinity,-2), uniform for very negative energy). Uniform form via the u = 1/c compactification constructed here.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- Uniform-in-energy convexity of the centered-left EH component away from the
critical energy: for every `η > 0` one mass radius works for all `c ≥ 2 + η`. -/
theorem eh_left_convex_body_away_from_critical (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → 2 + η ≤ c → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B ∧
          HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c) (frontier B) := by sorry

end BirkhoffGlobalSection
