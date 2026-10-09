-- Prove2me | Theorems.Thm_AffinePolicies_TwoGap_theorem_2
-- name    : AffinePolicies.TwoGap.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:39:32.942963+00:00
-- url     : https://prove2.me/theorems/b100bbd9-434f-4511-99a8-5af5fe646f77
-- title:
--   Theorem 2, PDF p. 9 — on the instance ℐ of (6), z_Aff(𝒰) > (2 − δ) · z_Adapt(𝒰)
-- statement:
--   Let $\delta > 0$ and let $m$ be an even integer with $m > 200/\delta^2$. Consider the instance $\mathcal I$ of $\Pi_{\mathrm{Adapt}}(\mathcal U)$ defined in (6): $n_1 = n_2 = m$, $c = 0$, $d = (1,\dots,1)^T$, $A = 0$, $B_{ii} = 1$ and $B_{ij} = 1/\sqrt m$ for $i \ne j$, and
--   $$\mathcal U=\operatorname{conv}\{0,e_1,\dots,e_m,b^{m+1},b^{m+2}\},$$
--   where $b^{m+1}$ equals $1/\sqrt m$ on the first $m/2$ coordinates and $0$ elsewhere, and $b^{m+2}$ equals $1/\sqrt m$ on the last $m/2$ coordinates and $0$ elsewhere. Then the worst-case cost of an optimal affine policy exceeds $(2-\delta)$ times the optimal worst-case cost of a fully adaptable solution:
--   $$z_{\mathrm{Aff}}(\mathcal U)>(2-\delta)\cdot z_{\mathrm{Adapt}}(\mathcal U).$$
--
--   Affine policies are optimal whenever the uncertainty set is a simplex, the convex hull of $m+1$ affinely independent points (Theorem 1 of the paper). Here $\mathcal U$ is the convex hull of $0$ and only $m+2$ other points, and the ratio of affine to adaptive cost can be made arbitrarily close to $2$; the optimality of affine policies for simplices is thus almost tight.
--
--   **Formalization Note** $z_{\mathrm{Adapt}}$ and $z_{\mathrm{Aff}}$ are infima of the worst-case bounds achieved by feasible (respectively feasible affine) solutions; the instance is feasible, so neither is a junk value. No hypothesis is added: for $\delta \ge 2$ the statement still holds, because the right-hand side is non-positive while every feasible solution costs at least $1$. Indices are 0-based, and $m/2$ is natural-number division, exact since $m$ is even.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 2, PDF p. 9 (instance (6), PDF p. 8; proof PDF pp. 13–15)

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.TwoGap

theorem theorem_2 (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm_even : Even m) (hm : 200 / δ ^ 2 < (m : ℝ)) :
    (2 - δ) * AffinePolicies.Simplex.zAdapt (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) <
      AffinePolicies.Simplex.zAff (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) := by sorry

end AffinePolicies.TwoGap
