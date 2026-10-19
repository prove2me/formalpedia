-- Prove2me | Theorems.Thm_ConfoundRobust_Minimax_lemma_4
-- name    : ConfoundRobust.Minimax.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:00.956514+00:00
-- url     : https://prove2.me/theorems/800e8eaa-7f1d-4496-a6fd-cbf2443e59af
-- title:
--   Lemma 4, p. 41 — uniform deviation over Π × monotone u, K depending only on the composition class's VC-major dimension (clipped bound reconstructed)
-- statement:
--   For every $v' \in \mathbb N$ there is a constant $K$, depending only on $v'$, with the following property. Let $\mu$ be the law of $(X,T,Y)$, $\Pi$ a class of policies, $\pi_0$ a baseline policy, and suppose the composition class
--   $$\bar{\mathcal U}^\Gamma = \big\{ (x,t,y) \mapsto u\big(y(\pi(t\mid x) - \pi_0(t\mid x))\big) : \pi \in \Pi,\ u : \mathbb R \to [0,1] \text{ nondecreasing} \big\}$$
--   has VC-major dimension at most $v'$ and is pointwise separable. Then for every $n \ge 1$ and $p \in (0, 1/2]$, with probability at least $1-p$ over an iid sample of size $n$,
--   $$\sup_{\pi \in \Pi,\ u} \frac1n \Big| \sum_{i=1}^n u\big(Y_i(\pi(T_i\mid X_i) - \pi_0(T_i\mid X_i))\big) - \mathbb E\big[u\big(Y(\pi(T\mid X) - \pi_0(T\mid X))\big)\big] \Big| \le \frac92 \sqrt K\, (v'+2) \sqrt{\frac{\log(1/p)}{n}} .$$
--
--   This is the joint uniform law over policies and monotone weights that the paper's proof of Theorem 6 uses for its weight terms.
--
--   **Formalization Note** The hypothesis is on the VC-major dimension of the composition class itself, as on the page ("$K_{u\circ\pi}$ that only depends on $v_{u\circ\pi}$"), not on that of $\Pi$: the paper's link between the two (Proposition 5) is false as printed. The printed bound is cut off by the right margin of PDF p. 41 after "$\sqrt{\log(1}$"; it is reconstructed as $\sqrt{\log(1/p)/n}$, as in Lemma 3. The statement is posed for $p \le 1/2$ for the same reason as Lemma 3. Pointwise separability of $\bar{\mathcal U}^\Gamma$ (a countable subclass approximating every member pointwise) is not printed; it is the standard measurability condition of the chaining argument the proof uses, and without it the statement fails (initial segments of $\omega_1$ under the countable–cocountable measure, with $u$ the identity on $\{0,1\}$ scores, give a VC-major class whose empirical deviation is $1$ for every sample).
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, Lemma 4, Appendix B.1, p. 41 (right side clipped; reconstructed)

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

namespace ConfoundRobust.Minimax

theorem lemma_4 :
    ∀ v' : ℕ, ∃ K : ℝ, ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (m n : ℕ), 0 < n →
      ∀ (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
        (Pol : Set (𝒳 → Fin m → ℝ)), (∀ π ∈ Pol, IsPolicy π) →
      ∀ π0 : 𝒳 → Fin m → ℝ, IsPolicy π0 → VCMajorLE (compClass Pol π0) v' →
        PointwiseSeparable (compClass Pol π0) →
      ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
      ∃ E : Set (Fin n → Obs 𝒳 m), MeasurableSet E ∧
        ENNReal.ofReal (1 - p) ≤ Measure.pi (fun _ : Fin n => μ) E ∧
        ∀ ω ∈ E, ∀ π ∈ Pol, ∀ u : ℝ → ℝ, IsUnitMonotone u →
          |(n : ℝ)⁻¹ * ∑ i, u (score π π0 (ω i)) - ∫ z, u (score π π0 z) ∂μ| ≤
            9 / 2 * Real.sqrt K * (v' + 2) * Real.sqrt (Real.log (1 / p) / n) := by sorry

end ConfoundRobust.Minimax
