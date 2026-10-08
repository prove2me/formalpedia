-- Prove2me | Theorems.Thm_AffinePolicies_LargeGap_claim_lambda_bounds
-- name    : AffinePolicies.LargeGap.claim_lambda_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:09:26.257053+00:00
-- url     : https://prove2.me/theorems/c54b9bb1-8159-4d41-a127-889a3742f13c
-- title:
--   Theorem 3, proof, first Claim, PDF p. 22 — 0 ≤ λ ≤ 1/m^{1/2+δ}
-- statement:
--   Let $\delta>0$ and $m^\delta>200$, and consider the instance (19). Let $\mu,\theta,\lambda\in\mathbb R$ and let $\hat P$ be the matrix with diagonal entries $\theta$ and off-diagonal entries $\mu$, and $\hat q=\lambda e$. Suppose that, for some first-stage $x$, the affine policy $\hat y(b)=\hat Pb+\hat q$ is feasible and its worst-case cost satisfies
--   $$\max_{b\in\mathcal U} d^\top(\hat Pb+\hat q)\le\frac{m^{1/2-\delta}}{4}\qquad\text{(assumption (27))}.$$
--   Then
--   $$0\le\lambda\le\frac{1}{m^{1/2+\delta}} .$$
--
--   This is the first of three bounds on the parameters of a symmetric affine policy in the proof by contradiction of Theorem 3.
--
--   **Formalization Note** On the page the claim is about the symmetric optimal solution of Lemma 8 under the contradiction hypothesis (27); here it is stated for every symmetric feasible affine policy satisfying (27), which is what the argument uses. Because Theorem 3 shows that no such policy exists, the hypotheses are jointly unsatisfiable; this is inherent in a step of a proof by contradiction, and proving the claim directly is the intended route.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 3, proof, (27) and first Claim, PDF p. 22–23

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

namespace AffinePolicies.LargeGap

theorem claim_lambda_bounds (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ)
    (x : Fin m → ℝ) (μ θ lam : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A19 m) (B19 m δ) (U19 m δ) x
      (AffinePolicies.Simplex.affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam)))
    (hcost : AffinePolicies.Simplex.CostLE (c19 m) (d19 m) (U19 m δ) x
      (AffinePolicies.Simplex.affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam))
      ((m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4)) :
    0 ≤ lam ∧ lam ≤ 1 / (m : ℝ) ^ ((1 : ℝ) / 2 + δ) := by sorry

end AffinePolicies.LargeGap
