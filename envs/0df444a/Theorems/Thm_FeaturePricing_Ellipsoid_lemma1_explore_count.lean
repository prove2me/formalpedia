-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_lemma1_explore_count
-- name    : FeaturePricing.Ellipsoid.lemma1_explore_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:32:38.22939+00:00
-- url     : https://prove2.me/theorems/1668a10c-393c-4517-91e2-eeaa0e8ff553
-- title:
--   Lemma 1, p. 15 — EllipsoidPricing explores in at most 2d² ln(20R(d+1)/ε) periods
-- statement:
--   Run EllipsoidPricing in dimension $d\ge2$ from $E_1=B(0,R)$, $R>0$, with parameter $0<\epsilon\le20R(d+1)$, on a feature sequence with $\|x_t\|\le1$ for all $t$, and true parameter $\|\theta\|\le R$ (Euclidean norms). Then for every horizon $T$, the number of periods $t\le T$ in which the algorithm chooses the explore price satisfies
--   $$
--   \#\{t\le T:\ \bar b_t-\underline b_t>\epsilon\}\ \le\ 2d^2\ln\!\Big(\frac{20R(d+1)}{\epsilon}\Big).
--   $$
--
--   Lemma 1 is the core of the regret analysis: exploitation periods cost at most $\epsilon$ each, so bounding the number of exploration periods bounds the regret.
--
--   **Formalization Note** The hypothesis $\epsilon\le20R(d+1)$ is not printed. Without it the right-hand side is negative while the count is nonnegative, so the printed lemma is false for larger $\epsilon$ (with $T\ge1$ and $x_t=0$ there are no explorations but the bound is $<0$); it is the initial eigenvalue floor used in the proof (p. 20). The count is cast to $\mathbb R$ and taken over Lean periods $t<T$ (paper periods $1,\dots,T$). The bound on $\theta$ is the standing normalization of §3; the count does not depend on it in the paper's argument.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 15, Lemma 1 (proof pp. 19–20)

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization

/-- **Lemma 1, p. 15.** EllipsoidPricing from `E₁ = B(0, R)` with `0 < ε ≤ 20R(d+1)` and features
`‖x_t‖ ≤ 1` (Euclidean) chooses the explore price in at most `2d² ln(20R(d+1)/ε)` periods: for
every horizon `T`, the number of exploration periods among the first `T` is at most that bound. -/
theorem lemma1_explore_count {d : ℕ} (hd : 2 ≤ d) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hεR : ε ≤ 20 * R * ((d : ℝ) + 1))
    (θ : Fin d → ℝ) (hθ : θ ⬝ᵥ θ ≤ R ^ 2) (x : ℕ → Fin d → ℝ) (hx : ∀ t, x t ⬝ᵥ x t ≤ 1)
    (T : ℕ) :
    open Classical in
    (((Finset.range T).filter (fun t => isExplore R ε θ x t)).card : ℝ) ≤
      2 * (d : ℝ) ^ 2 * Real.log (20 * R * ((d : ℝ) + 1) / ε) := by sorry

end FeaturePricing.Ellipsoid
