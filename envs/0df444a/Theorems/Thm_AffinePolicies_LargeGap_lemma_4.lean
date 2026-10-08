-- Prove2me | Theorems.Thm_AffinePolicies_LargeGap_lemma_4
-- name    : AffinePolicies.LargeGap.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:08:38.209537+00:00
-- url     : https://prove2.me/theorems/61d53fdc-4843-432c-bfdc-694d06bacd3c
-- title:
--   Lemma 4, PDF p. 17 — for the instance ℐ of (19), z_Adapt(𝒰) ≤ 1
-- statement:
--   Let $\delta>0$ and let $m$ satisfy $m^\delta>200$ (condition (18)). For the instance $\mathcal I$ of (19) — $c=0$, $d=e$, $A=0$, $B$ with unit diagonal and off-diagonal entries $\theta_0=m^{-(1-\delta)/2}$, and $\mathcal U$ the convex hull of $0$, the unit vectors $e_j$, $e/\sqrt m$ and the vectors $\theta_0\mathbf 1_S$ with $|S|=\lceil m^{1-\delta}\rceil$ — there is a feasible fully-adaptable solution $(x,y)$ whose worst-case cost is at most $1$; consequently
--   $$z_{\mathrm{Adapt}}(\mathcal U)\le 1 .$$
--
--   This upper bound on the fully-adaptable optimum is one half of the large gap of Theorem 3.
--
--   **Formalization Note** The existence of a feasible solution of cost at most $1$ is stated explicitly, so that the bound is not satisfied by the junk value of an empty infimum. The paper's own witness ($y=b$ at $0,e_j$ and $y=\frac1m e$ at the other generators) relies on $m^{(1-\delta)/2}\ge 1$, i.e. $\delta\le 1$; the statement is kept for every $\delta>0$, as on the page.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 4, PDF p. 17

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

namespace AffinePolicies.LargeGap

theorem lemma_4 (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) :
    (∃ (x : Fin m → ℝ) (y : (Fin m → ℝ) → Fin m → ℝ),
        AffinePolicies.Simplex.Feasible (A19 m) (B19 m δ) (U19 m δ) x y ∧ AffinePolicies.Simplex.CostLE (c19 m) (d19 m) (U19 m δ) x y 1) ∧
      AffinePolicies.Simplex.zAdapt (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) ≤ 1 := by sorry

end AffinePolicies.LargeGap
