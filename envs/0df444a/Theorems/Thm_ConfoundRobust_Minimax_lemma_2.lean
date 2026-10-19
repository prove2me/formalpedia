-- Prove2me | Theorems.Thm_ConfoundRobust_Minimax_lemma_2
-- name    : ConfoundRobust.Minimax.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:00.451024+00:00
-- url     : https://prove2.me/theorems/85d02f37-a9f2-483b-89a2-acd83049cbe5
-- title:
--   Lemma 2 (14), p. 39 — uniform deviation of (π(T|X) − 1/m)Y over Π: 9/2 C √K (v+2) √(log(5/δ)/n), K depending only on v
-- statement:
--   For every $v \in \mathbb N$ there is a constant $K$, depending only on $v$, with the following property. Let $\mu$ be the law of $(X,T,Y)$ with $m \ge 2$ treatments, let $\Pi$ be a class of policies whose VC-major dimension, as functions $(t,x) \mapsto \pi(t\mid x)$, is at most $v$ and which is pointwise separable as such a class, and suppose $|Y| \le C$ almost surely. For a policy $\pi$ let
--   $$f(\pi)(x,t,y) = \big(\pi(t\mid x) - \tfrac1m\big)\, y .$$
--   Then for every $n \ge 1$ and $\delta \in (0,1)$, with probability greater than $1-\delta$ over an iid sample of size $n$,
--   $$\sup_{\pi \in \Pi} \Big| \frac1n \sum_{i=1}^n \big(f_i(\pi) - \mathbb E[f(\pi)]\big) \Big| \le \frac92\, C \sqrt K\, (v+2) \sqrt{\frac{\log(5/\delta)}{n}},$$
--   where $f_i(\pi) = f(\pi)(X_i,T_i,Y_i)$.
--
--   This is the uniform law of large numbers for the policy class that controls the policy part of the regret decomposition in Theorem 6 (and in Theorem 2).
--
--   **Formalization Note** "With probability greater than $1-\delta$" is the existence of a measurable event of product measure $> 1-\delta$ on which the bound holds for all $\pi \in \Pi$ (inner probability, avoiding measurability of the supremum). The constant $K$ is chosen before everything except $v$. The page's envelope condition "$f(\pi) \le \|F\|_2 \le C$" is read as $|Y| \le C$ almost surely, which bounds $|f(\pi)| \le C$ since $|\pi(t\mid x) - 1/m| \le 1$; this is the case the paper uses ($C = B$). The page's "for $n$ large enough" is dropped: the proof (Dudley's entropy bound and Markov's inequality) does not use it. $\sqrt K (v+2)$ is read as printed; since $K$ is existential this is equivalent to $\sqrt{K(v+2)}$. **Measurability of the class.** The hypothesis that $\Pi$, as a class of functions $(t,x)\mapsto\pi(t\mid x)$, is pointwise separable (a countable subclass approximates every member pointwise; van der Vaart and Wellner 1996, Example 2.3.4) is not printed in the paper. It is the standard measurability condition under which the symmetrization and chaining tools the paper's proof uses hold, and it is necessary: on an uncountable well-ordered set of type $\omega_1$ with the countable–cocountable probability measure, the policies $\pi_\alpha(1\mid x) = \mathbb 1\{x \le \alpha\}$ form a class of VC-major dimension at most $2$, each $\pi_\alpha$ agrees almost surely with "never treat", yet $\alpha = \max_i X_i$ makes the empirical and population quantities differ by a fixed amount for every sample, so the statement without this hypothesis is false. Linear, logistic and finite-depth tree classes with real parameters are pointwise separable (rational parameters).
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, Lemma 2, display (14), Appendix B.1, p. 39 (f_i(π) defined on p. 38)

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

namespace ConfoundRobust.Minimax

theorem lemma_2 :
    ∀ v : ℕ, ∃ K : ℝ, ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (m n : ℕ), 2 ≤ m → 0 < n →
      ∀ (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
        (Pol : Set (𝒳 → Fin m → ℝ)), (∀ π ∈ Pol, IsPolicy π) → VCMajorLE (policyFns Pol) v →
        PointwiseSeparable (policyFns Pol) →
      ∀ C : ℝ, 0 ≤ C → (∀ᵐ z ∂μ, |z.2.2| ≤ C) →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ E : Set (Fin n → Obs 𝒳 m), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) < Measure.pi (fun _ : Fin n => μ) E ∧
        ∀ ω ∈ E, ∀ π ∈ Pol,
          |(n : ℝ)⁻¹ * ∑ i, fPol π (ω i) - ∫ z, fPol π z ∂μ| ≤
            9 / 2 * C * Real.sqrt K * (v + 2) * Real.sqrt (Real.log (5 / δ) / n) := by sorry

end ConfoundRobust.Minimax
