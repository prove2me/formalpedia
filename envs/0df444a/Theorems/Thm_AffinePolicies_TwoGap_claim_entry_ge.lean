-- Prove2me | Theorems.Thm_AffinePolicies_TwoGap_claim_entry_ge
-- name    : AffinePolicies.TwoGap.claim_entry_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:39:26.250434+00:00
-- url     : https://prove2.me/theorems/009b87df-db8b-4c42-b4b1-b1bea24699f6
-- title:
--   Theorem 2, proof, third Claim, PDF p. 15 — P̂_ij ≥ −(2 − δ)/m for all i, j
-- statement:
--   Let $\delta > 0$, let $m \ge 1$ be even and consider the instance $\mathcal I$ of (6). Let $x \in \mathbb R^m$, $\hat P \in \mathbb R^{m\times m}$ and $\beta \in \mathbb R$, and suppose that $x$ together with the affine policy $\hat y(b) = \hat Pb + \hat q$, where $\hat q_j = \beta$ for all $j$, is feasible and has worst-case cost at most $2-\delta$ on $\mathcal U$. Then
--   $$\hat P_{ij}\ge-\frac{2-\delta}{m}\qquad\text{for all } i,j\in\{1,\dots,m\}.$$
--
--   Together with the bound on the diagonal, this lower bound on every entry of $\hat P$ forces the policy to be expensive at the scenario $b^{m+1}$, which yields the contradiction in the proof of Theorem 2.
--
--   **Formalization Note** Stated for any feasible affine solution with constant intercept and worst-case cost at most $2-\delta$. The nonnegativity $\hat y(b) \ge 0$ on $\mathcal U$ that the proof invokes is part of feasibility.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 2, proof, third Claim (under (12)), PDF p. 15

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.TwoGap

theorem claim_entry_ge (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm_even : Even m) (hm0 : 0 < m)
    (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (β : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A6 m) (B6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)))
    (hcost : AffinePolicies.Simplex.CostLE (c6 m) (d6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)) (2 - δ)) :
    ∀ i j, -(2 - δ) / m ≤ P i j := by sorry

end AffinePolicies.TwoGap
