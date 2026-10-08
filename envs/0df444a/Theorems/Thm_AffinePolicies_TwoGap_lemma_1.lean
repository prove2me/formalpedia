-- Prove2me | Theorems.Thm_AffinePolicies_TwoGap_lemma_1
-- name    : AffinePolicies.TwoGap.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:38:54.777986+00:00
-- url     : https://prove2.me/theorems/1991ac85-f60e-4965-b2db-60042cb8f986
-- title:
--   Lemma 1, PDF p. 9 — on the instance ℐ of (6), z_Adapt(𝒰) ≤ 1
-- statement:
--   Let $m$ be an even natural number and consider the instance $\mathcal I$ of (6): $c = 0$, $d = e = (1,\dots,1)^T$, $A = 0$, $B_{ii} = 1$ and $B_{ij} = 1/\sqrt m$ for $i\neq j$, and $\mathcal U = \operatorname{conv}\{0, e_1,\dots,e_m, b^{m+1}, b^{m+2}\}$. Then there is a feasible fully-adaptable solution $(x, y(\cdot))$ of $\Pi_{\mathrm{Adapt}}(\mathcal U)$ whose worst-case cost is at most $1$, and consequently
--   $$z_{\mathrm{Adapt}}(\mathcal U)\le 1 .$$
--
--   This upper bound on the adaptive optimum is the adaptive side of the gap in Theorem 2.
--
--   **Formalization Note** The first conjunct (a feasible solution with worst-case cost at most $1$) is the solution the paper's proof constructs; stating it rules out the reading in which $z_{\mathrm{Adapt}}$ is $0$ because nothing is feasible. The condition $m > 200/\delta^2$ of the instance is not used by the lemma and is dropped, which makes the statement stronger.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 1, PDF p. 9

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.TwoGap

theorem lemma_1 (m : ℕ) (hm_even : Even m) :
    (∃ (x : Fin m → ℝ) (y : (Fin m → ℝ) → Fin m → ℝ),
      AffinePolicies.Simplex.Feasible (A6 m) (B6 m) (U6 m) x y ∧ AffinePolicies.Simplex.CostLE (c6 m) (d6 m) (U6 m) x y 1) ∧
    AffinePolicies.Simplex.zAdapt (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) ≤ 1 := by sorry

end AffinePolicies.TwoGap
