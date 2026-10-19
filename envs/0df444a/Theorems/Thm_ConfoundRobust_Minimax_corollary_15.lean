-- Prove2me | Theorems.Thm_ConfoundRobust_Minimax_corollary_15
-- name    : ConfoundRobust.Minimax.corollary_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:05.930106+00:00
-- url     : https://prove2.me/theorems/51168c8d-184c-4e3e-96ab-a2efdcf77804
-- title:
--   Corollary 15, p. 41 — Lemma 3 restricted to the treatment partition T = t (clipped bound reconstructed), p ≤ 1/2
-- statement:
--   Let $\mu$ be the law of $(X,T,Y)$, let $\pi$ and $\pi_0$ be fixed policies, $t$ a treatment, $n \ge 1$ and $p \in (0,1/2]$. With probability at least $1-p$ over an iid sample of size $n$,
--   $$\sup_{u} \frac1n \Big| \sum_{i=1}^n u\big(Y_i(\pi(T_i\mid X_i) - \pi_0(T_i\mid X_i))\big)\mathbb I[T_i = t] - \mathbb E\big[u\big(Y(\pi(T\mid X) - \pi_0(T\mid X))\big)\mathbb I[T = t]\big] \Big| \le 9 \sqrt{\frac{2\pi \log(1/p)}{n}},$$
--   the supremum over all nondecreasing $u : \mathbb R \to [0,1]$.
--
--   It is the per-treatment version of Lemma 3 used for the denominators of the Hájek ratios in the proof of Theorem 6.
--
--   **Formalization Note** The printed bound is cut off by the right margin of PDF p. 41 after "$9\sqrt{2\pi\,\mathrm{lo}$"; it is reconstructed as $9\sqrt{2\pi\log(1/p)/n}$, the bound of Lemma 3, of which the paper calls this "the restriction of the process to a specific treatment partition $t$" (p. 40). As for Lemma 3, the statement is posed for $p \le 1/2$, since it is false for $p$ near $1$.
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, Corollary 15, Appendix B.1, p. 41 (right side clipped; reconstructed from Lemma 3, p. 40)

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

namespace ConfoundRobust.Minimax

theorem corollary_15 {𝒳 : Type} [MeasurableSpace 𝒳] (m n : ℕ) (hn : 0 < n)
    (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
    (π π0 : 𝒳 → Fin m → ℝ) (hπ : IsPolicy π) (hπ0 : IsPolicy π0) (t : Fin m)
    (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    ∃ E : Set (Fin n → Obs 𝒳 m), MeasurableSet E ∧
      ENNReal.ofReal (1 - p) ≤ Measure.pi (fun _ : Fin n => μ) E ∧
      ∀ ω ∈ E, ∀ u : ℝ → ℝ, IsUnitMonotone u →
        |(n : ℝ)⁻¹ * ∑ i, (if (ω i).2.1 = t then u (score π π0 (ω i)) else 0) -
            ∫ z, (if z.2.1 = t then u (score π π0 z) else 0) ∂μ| ≤
          9 * Real.sqrt (2 * Real.pi * Real.log (1 / p) / n) := by sorry

end ConfoundRobust.Minimax
