-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoUniformly_of_tendsto_intervalIntegral_sq
-- name    : FiniteEnergyPlane.tendstoUniformly_of_tendsto_intervalIntegral_sq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T21:31:15.5165+00:00
-- url     : https://prove2.me/theorems/dd3a19c1-83e1-4a68-8f28-52c37e1e2852
-- title:
--   $L^2$ convergence of periodic loops with $L^2$-bounded derivatives is uniform
-- statement:
--   Let $E$ be a real Banach space. Let $f_k,f_k':\mathbb{R}\to E$ be such that, for all large $k$, $f_k$ is $1$-periodic and differentiable with continuous derivative $f_k'$, and $\int_0^1\|f_k'(t)\|^2\,dt\le M$. Let $e:\mathbb{R}\to E$ be continuous and $1$-periodic, and assume $\int_0^1\|f_k(t)-e(t)\|^2\,dt\to0$. Then $f_k\to e$ uniformly on $\mathbb{R}$.
--
--   This upgrades $L^2$ convergence of periodic loops with $L^2$-bounded derivatives to uniform convergence. It is used for `FiniteEnergyPlane.halfCyl_exists_subseq_tendsto_eigen`.
--
--   **Formalization Note** The hypotheses on $f_k$ hold `∀ᶠ k in atTop`. The derivative is given by `HasDerivAt (f k) (f' k t) t` for all `t`, and the conclusion is `TendstoUniformly f e atTop`.
-- source:
--   Standard (one-dimensional Sobolev embedding); used for C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Lemma 4.8.11

import Mathlib

open MeasureTheory Filter Topology

namespace FiniteEnergyPlane

/-- Eventually `1`-periodic `C¹` loops `f k` whose derivatives are eventually bounded in
`L²(0, 1)` and which converge in `L²(0, 1)` to a continuous `1`-periodic loop `e` converge to `e`
uniformly on `ℝ`. -/
theorem tendstoUniformly_of_tendsto_intervalIntegral_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f f' : ℕ → ℝ → E) (hf : ∀ᶠ k in atTop, ∀ t, HasDerivAt (f k) (f' k t) t)
    (hf' : ∀ᶠ k in atTop, Continuous (f' k)) (hper : ∀ᶠ k in atTop, Function.Periodic (f k) 1)
    (e : ℝ → E) (he : Continuous e) (hep : Function.Periodic e 1)
    (M : ℝ) (hM : ∀ᶠ k in atTop, ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤ M)
    (hL2 : Tendsto (fun k => ∫ t in (0:ℝ)..1, ‖f k t - e t‖ ^ 2) atTop (𝓝 0)) :
    TendstoUniformly f e atTop := by
  sorry

end FiniteEnergyPlane
