-- Prove2me | Theorems.Thm_Arxiv1302_0161_dp_well_posed
-- name    : Arxiv1302_0161.dp_well_posed
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:25:16.085253+00:00
-- url     : https://prove2.me/theorems/22d2b684-dcf9-4c7e-bd5e-1663bb6b62ab
-- title:
--   Theorem 2.5: well-posedness of the Dirichlet problem (DP)
-- statement:
--   Let $k>0$ and let $h_\Gamma\in C^2(\mathbb R)$ have compact support. Then there is a constant $C$ with the following property. For every incident direction $d\in S_-$, the Dirichlet problem (DP) with boundary data $f=-(u^i+u^r)$ has a solution $u^s\in C^2(D_+)\cap C(\overline{D_+})$ with
--
--   $$\sup_{x\in\overline{D_+}}|u^s(x)|\le C\,\|u^i+u^r\|_{C(\Gamma)},$$
--
--   and any two solutions coincide on $\overline{D_+}$.
--
--   **Formalization Note** As in Theorem 2.4, the constant is chosen before the incident direction. The sup norm on the right is written as: the bound holds with every upper bound $M$ of $|u^i+u^r|$ on $\Gamma$.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), claim c007; Section 2, Theorem 2.5, eq. (2.7), PDF p. 9

import Mathlib
import Definitions.Def_Arxiv1302_0161_Basic

open MeasureTheory Filter Topology

namespace Arxiv1302_0161

theorem dp_well_posed (k : ℝ) (hk : 0 < k) (h : ℝ → ℝ) (hh : IsLocalProfile h) :
    ∃ C : ℝ, ∀ d : R2, IsLowerDir d →
      (∃ u : R2 → ℂ, IsDPSolution k h (incData k d) u ∧
        ∀ M : ℝ, (∀ y ∈ Gam h, ‖uInc k d y + uRefl k d y‖ ≤ M) →
          ∀ x ∈ DplusClosed h, ‖u x‖ ≤ C * M) ∧
      ∀ u1 u2 : R2 → ℂ, IsDPSolution k h (incData k d) u1 → IsDPSolution k h (incData k d) u2 →
        ∀ x ∈ DplusClosed h, u1 x = u2 x := by sorry

end Arxiv1302_0161
