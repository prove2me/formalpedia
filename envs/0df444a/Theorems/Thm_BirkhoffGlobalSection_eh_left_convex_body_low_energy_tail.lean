-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_convex_body_low_energy_tail
-- name    : BirkhoffGlobalSection.eh_left_convex_body_low_energy_tail
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T15:12:48.942607+00:00
-- url     : https://prove2.me/theorems/15779d09-c473-4505-98a2-32d48e7723d1
-- title:
--   Uniform convexity of the EH component at very negative energy
-- statement:
--   There are $\varepsilon>0$ and a cutoff $C$ such that whenever
--
--   $$0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c\ge C,\qquad -c<h_1(\mu),$$
--
--   the selected centered-left EH component is the frontier of a compact convex body $B$ with $0\in\operatorname{int}B$, and $G_{\mu,c}$ has positive tangential Hessian on $\partial B$.
--
--   This is Liu--Salomão's "uniform strict convexity for very negative energy" (Section 10), for the explicit EH Hamiltonian.
--
--   **Intended proof.**
--   - **Rescaling.** Put $x=sX$ with $s=1/\sqrt c$, and write $G_{\mu,c}=G_{\mu,0}+\tfrac c4D$ with $D=\sinh^2x_1+\sin^2x_2$. Then $\hat G_s(X,y)=G_{\mu,1/s^2}(sX,y)$ satisfies
--   $$d^2\hat G_s[v,v]=d^2G_{\mu,0}(L_sy)[L_sv,L_sv]+\tfrac14\,d^2D(sX)[v_X,v_X],\qquad L_s=\operatorname{diag}(s,s,1,1).$$
--   The first derivative and the value extend the same way, through $\sinh(st)/s$ and $\sin(st)/s$. All of them are jointly continuous through $s=0$.
--   - **The limit $s=0$.** It is the explicit ellipsoid $\tfrac12|y|^2+\tfrac14|X|^2=1-\mu$, with Hessian $\operatorname{diag}(\tfrac12,\tfrac12,1,1)$ and radial derivative $|y|^2+\tfrac12|X|^2$.
--   - **Tube lemma.** The tube lemma of `BirkhoffGlobalSection_EHConvexPerturbation` at $(\mu,s)=(\tfrac12,0)$ gives strict star-shapedness, a box barrier and a positive tangential Hessian for $s$ small. Since $L_s$ is linear, these transfer back. The radial-graph and convex-body steps follow as in the local leaves.
--
--   This uses neither Theorem 9.4 nor any estimate at moderate energies.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S10, third paragraph, final sentence (uniform strict convexity for very negative energy). Rescaled-limit (ellipsoid) argument constructed here.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- Convexity of the centered-left EH component at very negative energy, uniformly:
near equal masses and for all sufficiently large `c`, the component bounds a compact
convex body with positive tangential Hessian on its frontier. -/
theorem eh_left_convex_body_low_energy_tail :
    ∃ ε C : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → C ≤ c → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B ∧
          HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c) (frontier B) := by sorry

end BirkhoffGlobalSection
