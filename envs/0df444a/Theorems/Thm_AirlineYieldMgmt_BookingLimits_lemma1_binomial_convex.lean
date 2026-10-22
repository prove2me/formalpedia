-- Prove2me | Theorems.Thm_AirlineYieldMgmt_BookingLimits_lemma1_binomial_convex
-- name    : AirlineYieldMgmt.BookingLimits.lemma1_binomial_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:12:27.870453+00:00
-- url     : https://prove2.me/theorems/e0dc6e73-422e-438d-8763-fbcdd0e851e9
-- title:
--   Lemma 1 — E[f(Bin(x, γ))] is nondecreasing and convex in x when f is nondecreasing and convex
-- statement:
--   Let $f(y)$, $y \ge 0$, be nondecreasing and convex, and let $0 < \gamma < 1$. For each non-negative integer $x$ let $Y(x)$ be a binomial-$(x,\gamma)$ random variable and
--   $$h(x) \;=\; \mathrm{E}\,f(Y(x)) \;=\; \sum_{k=0}^{x}\binom{x}{k}\gamma^k(1-\gamma)^{x-k} f(k).$$
--   Then $h$ is nondecreasing and convex on $\{0,1,2,\dots\}$:
--   $$h(x) \le h(x+1) \quad\text{and}\quad h(x+1) - h(x) \;\le\; h(x+2) - h(x+1)\qquad \text{for all } x \ge 0.$$
--   In the paper this lemma (quoted from Shaked and Shanthikumar, 1994, Example 6.A.2) is what makes the terminal value $U_0$ concave and nonincreasing, which starts the induction behind the booking-limit result.
--
--   **Formalization Note.** $f : \mathbb R \to \mathbb R$ with `MonotoneOn f (Set.Ici 0)` and `ConvexOn ℝ (Set.Ici 0) f`, the paper's "$f(y)$, $y \ge 0$". The expectation is the finite binomial sum `binomExp x γ f`. Convexity in $x \in \{0,1,\dots\}$ is stated as the discrete second-difference inequality, not as convexity of a real interpolation.
-- source:
--   Subramanian, Stidham, Lautenbacher, Airline Yield Management with Overbooking, Cancellations, and No-Shows, Transp. Sci. 33(2), 1999, p. 151, Lemma 1

import Mathlib
import Definitions.Def_AirlineYieldMgmt_BookingLimits_Model

namespace AirlineYieldMgmt.BookingLimits

/-- Lemma 1 (p. 151). If `f(y)`, `y ≥ 0`, is nondecreasing and convex and `0 < γ < 1`, then
`h(x) := E[f(Y(x))]` with `Y(x) ∼ Bin(x, γ)` is nondecreasing and (discretely) convex in
`x ∈ {0, 1, …}`. -/
theorem lemma1_binomial_convex (f : ℝ → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_convex : ConvexOn ℝ (Set.Ici 0) f) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Monotone (fun x : ℕ => binomExp x γ f) ∧
      ∀ x : ℕ, binomExp (x + 1) γ f - binomExp x γ f ≤
        binomExp (x + 2) γ f - binomExp (x + 1) γ f := by sorry

end AirlineYieldMgmt.BookingLimits
