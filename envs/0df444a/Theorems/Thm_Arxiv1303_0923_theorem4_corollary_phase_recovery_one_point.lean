-- Prove2me | Theorems.Thm_Arxiv1303_0923_theorem4_corollary_phase_recovery_one_point
-- name    : Arxiv1303_0923.theorem4_corollary_phase_recovery_one_point
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:35:38.8429+00:00
-- url     : https://prove2.me/theorems/7a4cea48-97fb-44cf-9d45-e9c773c25d2b
-- title:
--   Remark 1 (corollary of Theorem 4): one receiver point with $q(\tilde x)\neq0$ recovers the complex scattered field
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $g$ satisfy (13), (14). Let $q_1,q_2$ satisfy (3), (4) with $m=4$ and $q_1=q_2=q$ in $\mathbb{R}^3\setminus\Omega$. For $j=1,2$ and every real $k$ let $v_j(\cdot,k)\in C^5(\mathbb{R}^3)$ be the solution of (15)-(17) with $q=q_j$, and let $v_{s,j}=v_j-v_0$. Let $(a,b)$, $a<b$, be an interval. Fix $\tilde x\in S$ with $q(\tilde x)\neq0$ and assume
--   $$|v_{s,1}(\tilde x,k)|^2=|v_{s,2}(\tilde x,k)|^2\qquad\forall k\in(a,b).$$
--   Then $v_{s,1}(\tilde x,k)=v_{s,2}(\tilde x,k)$ for all $k\in\mathbb{R}$.
--
--   This is the corollary of Theorem 4 announced in Remark 1, proved at the end of Section 5.3: the modulus of the scattered wave at one point of $S$ determines the complex scattered wave at that point.
--
--   **Formalization Note** The paper does not write this corollary out. Following the recorded claim and the proof, which divides only by $(qg)(\tilde x)$, the nonvanishing of $q$ is assumed only at $\tilde x$ and not on all of $S$.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c015; Section 1.1, Remark 1, PDF p. 3; proved at the end of Section 5.3, p. 18

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem theorem4_corollary_phase_recovery_one_point (geo : Geometry) (g : R3 → ℝ)
    (hg : IsSourceTerm geo g) (q1 q2 q : R3 → ℝ)
    (hq1 : IsPotential geo.G 4 q1) (hq2 : IsPotential geo.G 4 q2)
    (h1 : ∀ x, x ∉ geo.Om → q1 x = q x) (h2 : ∀ x, x ∉ geo.Om → q2 x = q x)
    (v1 v2 : R3 → ℝ → ℂ)
    (hv1 : ∀ k : ℝ, IsSourceSolution q1 g k (fun x => v1 x k))
    (hv2 : ∀ k : ℝ, IsSourceSolution q2 g k (fun x => v2 x k))
    (a b : ℝ) (hab : a < b) (xt : R3) (hxt : xt ∈ geo.S) (hqxt : q xt ≠ 0)
    (hdata : ∀ k ∈ Set.Ioo a b,
      ‖v1 xt k - bgField geo.G g xt k‖ ^ 2 = ‖v2 xt k - bgField geo.G g xt k‖ ^ 2) :
    ∀ k : ℝ, v1 xt k - bgField geo.G g xt k = v2 xt k - bgField geo.G g xt k := by sorry

end Arxiv1303_0923
