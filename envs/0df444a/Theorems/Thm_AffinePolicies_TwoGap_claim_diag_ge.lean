-- Prove2me | Theorems.Thm_AffinePolicies_TwoGap_claim_diag_ge
-- name    : AffinePolicies.TwoGap.claim_diag_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:39:21.403673+00:00
-- url     : https://prove2.me/theorems/608fc231-d436-43ed-a559-d597c312c21f
-- title:
--   Theorem 2, proof, second Claim, PDF pp. 13–14 — P̂_jj ≥ 1 − 2/√m − 2/m for all j
-- statement:
--   Let $\delta > 0$, let $m \ge 1$ be even and consider the instance $\mathcal I$ of (6). Let $x \in \mathbb R^m$, $\hat P \in \mathbb R^{m\times m}$ and $\beta \in \mathbb R$, and suppose that $x$ together with the affine policy $\hat y(b) = \hat Pb + \hat q$, where $\hat q_j = \beta$ for all $j$, is feasible and has worst-case cost at most $2-\delta$ on $\mathcal U$. Then for every $j = 1,\dots,m$,
--   $$\hat P_{jj}\ge 1-\frac{2}{\sqrt m}-\frac{2}{m}.$$
--
--   The diagonal of $\hat P$ must be close to $1$ because the policy has to cover each unit scenario $e_j$ cheaply; this bound is one of the two inputs of the estimate (16) in the proof of Theorem 2.
--
--   **Formalization Note** Stated for any feasible affine solution with constant intercept and worst-case cost at most $2-\delta$, which is what the proof uses about the symmetric optimal solution under assumption (12). Indices are 0-based in Lean.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 2, proof, second Claim (under (12)), PDF pp. 13–14

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.TwoGap

theorem claim_diag_ge (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm_even : Even m) (hm0 : 0 < m)
    (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (β : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A6 m) (B6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)))
    (hcost : AffinePolicies.Simplex.CostLE (c6 m) (d6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)) (2 - δ)) :
    ∀ j, 1 - 2 / Real.sqrt m - 2 / m ≤ P j j := by sorry

end AffinePolicies.TwoGap
