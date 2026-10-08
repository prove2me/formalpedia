-- Prove2me | Theorems.Thm_AffinePolicies_TwoGap_claim_beta_le
-- name    : AffinePolicies.TwoGap.claim_beta_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:39:31.134784+00:00
-- url     : https://prove2.me/theorems/e00a1257-83c7-4e75-be35-eb8d2d2a1a26
-- title:
--   Theorem 2, proof, first Claim, PDF p. 13 — an affine solution with q̂ ≡ β and cost ≤ 2 − δ has β ≤ (2 − δ)/m
-- statement:
--   Let $\delta > 0$, let $m \ge 1$ be even and consider the instance $\mathcal I$ of (6). Let $x \in \mathbb R^m$, $\hat P \in \mathbb R^{m\times m}$ and $\beta \in \mathbb R$, and suppose that $x$ together with the affine policy $\hat y(b) = \hat Pb + \hat q$, where $\hat q_j = \beta$ for all $j$, is feasible and has worst-case cost at most $2 - \delta$:
--   $$c^Tx+d^T\hat y(b)\le 2-\delta\qquad\text{for all } b\in\mathcal U .$$
--   Then
--   $$\beta\le\frac{2-\delta}{m}.$$
--
--   This is the first step of the contradiction argument proving Theorem 2, in which the cost bound is assumption (12), $z_{\mathrm{Aff}}(\mathcal U) \le 2-\delta$, applied to the symmetric optimal affine solution of Lemma 3.
--
--   **Formalization Note** The claim is stated for any feasible affine solution with constant intercept $\beta$ and worst-case cost at most $2-\delta$, which is exactly what the paper's proof uses about $\hat y$. The hypothesis $m > 0$ excludes the empty instance and the division by zero.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 2, proof, first Claim (under (12)), PDF p. 13

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.TwoGap

theorem claim_beta_le (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm_even : Even m) (hm0 : 0 < m)
    (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (β : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A6 m) (B6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)))
    (hcost : AffinePolicies.Simplex.CostLE (c6 m) (d6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)) (2 - δ)) :
    β ≤ (2 - δ) / m := by sorry

end AffinePolicies.TwoGap
