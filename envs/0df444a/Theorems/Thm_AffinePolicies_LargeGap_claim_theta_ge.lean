-- Prove2me | Theorems.Thm_AffinePolicies_LargeGap_claim_theta_ge
-- name    : AffinePolicies.LargeGap.claim_theta_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:09:37.027718+00:00
-- url     : https://prove2.me/theorems/b746b228-fe60-4bad-967a-526ee471fc94
-- title:
--   Theorem 3, proof, second Claim, PDF p. 23 — θ ≥ 1/3
-- statement:
--   Let $\delta>0$ and $m^\delta>200$, and consider the instance (19). Let $\mu,\theta,\lambda\in\mathbb R$, let $\hat P$ have diagonal entries $\theta$ and off-diagonal entries $\mu$, and let $\hat q=\lambda e$. If for some first-stage $x$ the affine policy $\hat y(b)=\hat Pb+\hat q$ is feasible and
--   $$\max_{b\in\mathcal U} d^\top(\hat Pb+\hat q)\le\frac{m^{1/2-\delta}}{4}\qquad\text{(27)},$$
--   then
--   $$\theta\ge\frac13 .$$
--
--   This is the second parameter bound in the proof by contradiction of Theorem 3: the diagonal of the symmetric policy must carry most of the response to a unit demand $e_j$.
--
--   **Formalization Note** As for the first Claim, the statement covers every symmetric feasible affine policy satisfying (27) rather than only the optimal one of Lemma 8; the hypotheses are jointly unsatisfiable by Theorem 3, as is inherent in a step of a proof by contradiction.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 3, proof, second Claim, PDF p. 23–24

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

namespace AffinePolicies.LargeGap

theorem claim_theta_ge (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ)
    (x : Fin m → ℝ) (μ θ lam : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A19 m) (B19 m δ) (U19 m δ) x
      (AffinePolicies.Simplex.affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam)))
    (hcost : AffinePolicies.Simplex.CostLE (c19 m) (d19 m) (U19 m δ) x
      (AffinePolicies.Simplex.affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam))
      ((m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4)) :
    1 / 3 ≤ θ := by sorry

end AffinePolicies.LargeGap
