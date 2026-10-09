-- Prove2me | Theorems.Thm_CustAssort_Value_theorem_3_1
-- name    : CustAssort.Value.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:27.692975+00:00
-- url     : https://prove2.me/theorems/bc8d13f9-bf83-42ae-8149-1acdeae6972f
-- title:
--   Theorem 3.1, p. 7 — customization gains at most a factor m, and the order is tight
-- statement:
--   Let $n$ products have positive revenues, nonnegative type-dependent MNL preference weights, and a no-purchase weight of one. Let the $m$ customer types arrive with nonnegative probabilities summing to one. For a first-stage assortment of size at most $K$, $z_{\rm CAP}$ permits a separate subset for each type, while $z_{\rm MMNL}$ offers the same assortment to every type. Then
--
--   $$z_{\rm MMNL}\le z_{\rm CAP}\le m\,z_{\rm MMNL}.$$
--
--   The order is tight: for every $m\ge2$, the paper's family with $n=K=m$, $b=m-1$, $a=2m(m-1)^m$, $\theta_j=\alpha/a^j$, $r_i=a^i$, and $v_{ij}=b^{m-i+1}$ when $i\le j$ (zero otherwise), satisfies the model assumptions and has $z_{\rm MMNL}>0$ and
--
--   $$z_{\rm CAP}\ge\frac{m}{6}\,z_{\rm MMNL}.$$
--
--   This compares the best expected revenue with and without customer-type customization. The explicit family realizes the paper's $\Omega(m)$ assertion with a positive MMNL benchmark.
--
--   **Formalization Note** Products and types are 0-based `Fin` indices. The explicit constant $1/6$ is pinned from the proof's bounds $z_{\rm CAP}\ge\alpha m/2$ and $z_{\rm MMNL}\le3\alpha$. No revenue-order hypothesis is imposed: the instance has increasing revenues.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082 (version of December 7, 2021), p. 7, Theorem 3.1; proof pp. 7–9

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

namespace CustAssort.Value

/-- Theorem 3.1, page 7, including the explicit tightness family of pages 8–9. -/
theorem theorem_3_1 :
    (∀ (n m K : ℕ) (r : Fin n → ℝ) (v : Fin n → Fin m → ℝ)
      (θ : Fin m → ℝ),
      (∀ i, 0 < r i) → (∀ i j, 0 ≤ v i j) → (∀ j, 0 ≤ θ j) →
      (∑ j : Fin m, θ j) = 1 →
      zMMNL θ v r K ≤ zCAP θ v r K ∧
      zCAP θ v r K ≤ (m : ℝ) * zMMNL θ v r K) ∧
    (∀ m : ℕ, 2 ≤ m →
      (∀ i : Fin m, 0 < revI (aStar m) m i) ∧
      (∀ i j : Fin m, 0 ≤ vI (bStar m) m i j) ∧
      (∀ j : Fin m, 0 ≤ thetaI (aStar m) m j) ∧
      (∑ j : Fin m, thetaI (aStar m) m j) = 1 ∧
      0 < zMMNL (thetaI (aStar m) m) (vI (bStar m) m)
        (revI (aStar m) m) m ∧
      (m : ℝ) / 6 * zMMNL (thetaI (aStar m) m) (vI (bStar m) m)
        (revI (aStar m) m) m ≤
      zCAP (thetaI (aStar m) m) (vI (bStar m) m)
        (revI (aStar m) m) m) := by sorry

end CustAssort.Value
