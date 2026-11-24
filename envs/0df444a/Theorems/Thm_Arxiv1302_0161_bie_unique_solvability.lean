-- Prove2me | Theorems.Thm_Arxiv1302_0161_bie_unique_solvability
-- name    : Arxiv1302_0161.bie_unique_solvability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:24:41.161801+00:00
-- url     : https://prove2.me/theorems/98ed9cf3-d9c7-4825-ac64-590116b2eaf8
-- title:
--   Theorem 2.4: unique solvability of the integral equation $P\varphi=g$
-- statement:
--   Let $k>0$, let $\eta\neq0$ be real, let $h_\Gamma\in C^2(\mathbb R)$ have compact support, and let $R>0$ with $\Gamma_p\subset B_R$. Then there is a constant $C$ with the following property. For every incident direction $d\in S_-$, the integral equation $P\varphi=g$ of (2.3)–(2.4) has a solution $\varphi\in C(\partial D_R^-)$ with
--
--   $$\|\varphi\|_{C(\partial D_R^-)}\le C\,\|u^i+u^r\|_{C(\Gamma)},$$
--
--   and any two solutions in $C(\partial D_R^-)$ coincide on $\partial D_R^-$.
--
--   This is the main result of the paper. The equation lives on a bounded curve with two corners, and it involves neither an infinite integral nor a Dirichlet-to-Neumann map.
--
--   **Formalization Note** The constant $C$ is chosen before the incident direction, so it does not depend on the incident field. It may depend on $k$, $\eta$, $R$ and $h_\Gamma$. The paper does not state this dependence; this is the reading under which (2.5) has content. The sup norm on the right is written as: the bound holds with every upper bound $M$ of $|u^i+u^r|$ on $\Gamma$.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), claim c006; Section 2, Theorem 2.4, eq. (2.5), PDF p. 6 (proof pp. 6-9)

import Mathlib
import Definitions.Def_Arxiv1302_0161_Basic

open MeasureTheory Filter Topology

namespace Arxiv1302_0161

theorem bie_unique_solvability (k : ℝ) (hk : 0 < k) (eta : ℝ) (heta : eta ≠ 0)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R) :
    ∃ C : ℝ, ∀ d : R2, IsLowerDir d →
      (∃ phi : R2 → ℂ, ContinuousOn phi (bdry h R) ∧
        (∀ x ∈ bdry h R, opP k eta h R phi x = gData k d h R x) ∧
        ∀ M : ℝ, (∀ y ∈ Gam h, ‖uInc k d y + uRefl k d y‖ ≤ M) →
          ∀ x ∈ bdry h R, ‖phi x‖ ≤ C * M) ∧
      ∀ phi1 phi2 : R2 → ℂ, ContinuousOn phi1 (bdry h R) → ContinuousOn phi2 (bdry h R) →
        (∀ x ∈ bdry h R, opP k eta h R phi1 x = gData k d h R x) →
        (∀ x ∈ bdry h R, opP k eta h R phi2 x = gData k d h R x) →
        ∀ x ∈ bdry h R, phi1 x = phi2 x := by sorry

end Arxiv1302_0161
