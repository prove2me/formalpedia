-- Prove2me | Theorems.Thm_BSSSampleRobust_Asymptotic_lemma_EC2
-- name    : BSSSampleRobust.Asymptotic.lemma_EC2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:27:52.056885+00:00
-- url     : https://prove2.me/theorems/91e36427-4933-4699-991a-29c43e7e33f3
-- title:
--   Lemma EC.2 — Empirical Wasserstein bound
-- statement:
--   Fix $d\ge1$, any $\ell_p$ norm, a measurable $f:\mathbb R^d\to\mathbb R$, a set $Z\subseteq\mathbb R^d$, and $N\ge1$ observations $\hat\xi^j\in Z$, with repetitions permitted. Let $\widehat P_N$ be their uniform empirical law and $\mathcal P(Z)$ the probability laws assigning mass one to $Z$. If $\theta_2\ge2\theta_1\ge0$, then
--   $$\sup_{Q\in\mathcal P(Z):W_1(Q,\widehat P_N)\le\theta_1}E_Q[f(\xi)]
--   \le\frac1N\sum_{j=1}^N\sup_{z\in Z:\|z-\hat\xi^j\|\le\theta_2}f(z)
--   +\frac{4\theta_1}{\theta_2}\sup_{z\in Z}|f(z)|.$$
--   The extended-valued estimate applies to unbounded measurable functions and has the printed coefficient 4.
--
--   Differences from the source:
--   - encoding: finite-dimensional real spaces with any fixed lp norm, 1 ≤ p ≤ ∞ → PiLp over finite coordinates, Borel sigma algebras, and Fact (1 ≤ p); reason: coordinate relabeling preserves every allowed norm and every source instance; the ambient dimension is positive
--   - encoding: extended-real expectation and extrema with infinity minus infinity equal to positive infinity → EReal extrema and the referenced positive-part-first expectation, applied on the completed measure; reason: infeasibility gives positive infinity and unbounded extrema remain infinite; no integrability hypothesis is added
--   - reading: expectations of local suprema and indicators, with page 6 defining set probability as indicator expectation but not specifying completion → completed lower-integral expectations; concentration and retained-set probabilities are expectations of indicators; reason: this preserves the explicit indicator identity without imposing measurability, closedness, continuity, or boundedness; on completed-measurable sets it is the ordinary probability
--   - encoding: samples indexed 1 through N, N positive, under the infinite iid product law → samples indexed by Fin N, drawn from the coordinates 0 through N-1 of Measure.infinitePi on natural numbers; reason: a shift of labels gives the same iid data; finite-sample assertions require N ≥ 1 and asymptotic assertions ignore N = 0
--   - reading: theta2 ≥ 2 theta1 ≥ 0 with a quotient and a possibly infinite absolute supremum → real division gives 0/0 = 0, and scale explicitly gives 0 times any extended value = 0; reason: the printed formula leaves the zero-radius boundary unspecified; at radius zero the admissible law equals the empirical law or the single-center Dirac law
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; Lemma EC.2, PDF page 59, printed page ec17

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Sampling

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BSSSampleRobust.Asymptotic

theorem lemma_EC2 (p : ℝ≥0∞) [Fact (1 ≤ p)] (d : ℕ) (hd : 0 < d)
    (f : Vec p (Fin d) → ℝ) (hf : Measurable f)
    (Z : Set (Vec p (Fin d))) (N : ℕ) (hN : 1 ≤ N)
    (data : Fin N → Vec p (Fin d)) (hdata : ∀ j, data j ∈ Z)
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 ≤ θ₁) (hθ₂ : 2 * θ₁ ≤ θ₂) :
    transportWorst Z (WassersteinDRO.Duality.empiricalDistribution data) θ₁
        (fun z => (f z : EReal)) ≤
      average (fun j => supremum {z | z ∈ Z ∧ ‖z - data j‖ ≤ θ₂} f) +
      scale (4 * θ₁ / θ₂) (absSup Z f) := by sorry

end BSSSampleRobust.Asymptotic
