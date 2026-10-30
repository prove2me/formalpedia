-- Prove2me | Theorems.Thm_BSSSampleRobust_Asymptotic_lemma_EC1
-- name    : BSSSampleRobust.Asymptotic.lemma_EC1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:27:44.641979+00:00
-- url     : https://prove2.me/theorems/c0774702-d7a4-4da0-b6e9-d84625ebbb80
-- title:
--   Lemma EC.1 — Single-center moment bound
-- statement:
--   Fix $d\ge1$, any $\ell_p$ norm with $1\le p\le\infty$, a measurable $f:\mathbb R^d\to\mathbb R$, any set $Z\subseteq\mathbb R^d$, and a center $c\in Z$. For real radii $\theta_2\ge2\theta_1\ge0$,
--   $$\sup_{Q\in\mathcal P(Z):E_Q\|\xi-c\|\le\theta_1}E_Q[f(\xi)]
--   \le\sup_{z\in Z:\|z-c\|\le\theta_2}f(z)+\frac{2\theta_1}{\theta_2}\sup_{z\in Z}|f(z)|.$$
--   Here $\mathcal P(Z)$ consists of probability laws assigning mass one to $Z$. Expectations and suprema take extended-real values, and $f$ need not be bounded. This is the single-center estimate with the source's coefficient 2.
--
--   Differences from the source:
--   - encoding: finite-dimensional real spaces with any fixed lp norm, 1 ≤ p ≤ ∞ → PiLp over finite coordinates, Borel sigma algebras, and Fact (1 ≤ p); reason: coordinate relabeling preserves every allowed norm and every source instance; the ambient dimension is positive
--   - encoding: extended-real expectation and extrema with infinity minus infinity equal to positive infinity → EReal extrema and the referenced positive-part-first expectation, applied on the completed measure; reason: infeasibility gives positive infinity and unbounded extrema remain infinite; no integrability hypothesis is added
--   - reading: expectations of local suprema and indicators, with page 6 defining set probability as indicator expectation but not specifying completion → completed lower-integral expectations; concentration and retained-set probabilities are expectations of indicators; reason: this preserves the explicit indicator identity without imposing measurability, closedness, continuity, or boundedness; on completed-measurable sets it is the ordinary probability
--   - reading: theta2 ≥ 2 theta1 ≥ 0 with a quotient and a possibly infinite absolute supremum → real division gives 0/0 = 0, and scale explicitly gives 0 times any extended value = 0; reason: the printed formula leaves the zero-radius boundary unspecified; at radius zero the admissible law equals the empirical law or the single-center Dirac law
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; Lemma EC.1, PDF page 57, printed page ec15

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Sampling

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BSSSampleRobust.Asymptotic

theorem lemma_EC1 (p : ℝ≥0∞) [Fact (1 ≤ p)] (d : ℕ) (hd : 0 < d)
    (f : Vec p (Fin d) → ℝ) (hf : Measurable f)
    (Z : Set (Vec p (Fin d))) (c : Vec p (Fin d)) (hc : c ∈ Z)
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 ≤ θ₁) (hθ₂ : 2 * θ₁ ≤ θ₂) :
    momentWorst Z c θ₁ f ≤
      supremum {z | z ∈ Z ∧ ‖z - c‖ ≤ θ₂} f +
      scale (2 * θ₁ / θ₂) (absSup Z f) := by sorry

end BSSSampleRobust.Asymptotic
