-- Prove2me | Theorems.Thm_Arxiv1302_0161_bie_solution_solves_dp
-- name    : Arxiv1302_0161.bie_solution_solves_dp
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:24:04.976084+00:00
-- url     : https://prove2.me/theorems/590a865e-a66d-4a5a-8586-3b7806fd8c83
-- title:
--   Lemma 2.3: a solution of $P\varphi=g$ gives the solution of (DP)
-- statement:
--   Let $k>0$, let $\eta\neq0$ be real, let $h_\Gamma\in C^2(\mathbb R)$ have compact support, and let $R>0$ with $\Gamma_p\subset B_R$. Let $d\in S_-$. Suppose $\varphi\in C(\partial D_R^-)$ satisfies $P\varphi=g$ on $\partial D_R^-$, with $P$ and $g$ as in (2.3) and (2.4). Consider the function
--
--   $$u^s=\mathcal D_k\varphi-i\eta\,\mathcal S_k\varphi\quad\text{on }D_+.$$
--
--   Then $u^s$ extends continuously to $\overline{D_+}$, and the extension lies in $C^2(D_+)\cap C(\overline{D_+})$ and solves (DP) with $f=-(u^i+u^r)$. That is, it solves the Helmholtz equation in $D_+$, satisfies the Sommerfeld radiation condition, and equals $-(u^i+u^r)$ on the whole surface $\Gamma$.
--
--   **Formalization Note** On $\Gamma_R$ the formula for $u^s$ gives the direct value of the integral, not the limit from $D_+$. The statement therefore asserts that some function equal to $\mathcal D_k\varphi-i\eta\mathcal S_k\varphi$ on $D_+$ solves (DP). This is the paper's continuous extension to $\overline{D_+}$.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), claim c005; Section 2, Lemma 2.3, eqs. (2.2)-(2.4), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1302_0161_Basic

open MeasureTheory Filter Topology

namespace Arxiv1302_0161

theorem bie_solution_solves_dp (k : ℝ) (hk : 0 < k) (eta : ℝ) (heta : eta ≠ 0)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R)
    (d : R2) (hd : IsLowerDir d) (phi : R2 → ℂ) (hphi : ContinuousOn phi (bdry h R))
    (hP : ∀ x ∈ bdry h R, opP k eta h R phi x = gData k d h R x) :
    ∃ U : R2 → ℂ, (∀ x ∈ Dplus h, U x = combinedPot k eta h R phi x) ∧
      IsDPSolution k h (incData k d) U := by sorry

end Arxiv1302_0161
