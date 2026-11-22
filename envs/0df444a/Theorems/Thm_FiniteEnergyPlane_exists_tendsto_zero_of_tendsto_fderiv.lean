-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tendsto_zero_of_tendsto_fderiv
-- name    : FiniteEnergyPlane.exists_tendsto_zero_of_tendsto_fderiv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T18:16:26.476922+00:00
-- url     : https://prove2.me/theorems/50b0446d-0574-462b-a185-c15bf545e15d
-- title:
--   Persistence of a nondegenerate zero under C^1-small perturbations
-- statement:
--   Let $E$ be a real Banach space, $F$ a real normed space, and $f:E\to F$ strictly differentiable at $p$ with derivative a continuous linear isomorphism $L:E\to F$, and $f(p)=0$. Let $h_k:E\to F$ be differentiable on a ball $B(p,\delta_0)$, with $h_k(p)\to0$ and $Dh_k\to0$ uniformly on $B(p,\delta_0)$. Then there is $\delta>0$ such that $f+h_k$ is injective on $B(p,\delta)$ for all large $k$, and there are points $x_k\to p$ with $f(x_k)+h_k(x_k)=0$ for all large $k$.
--
--   A nondegenerate zero persists, and stays locally unique, under perturbations that are small in $C^1$ near the zero. It is used to locate intersections of Reeb trajectories with nearby planes (Hryniewicz 2012, Lemmas 7.2 and 7.3).
--
--   **Formalization Note** "Strictly differentiable" is `HasStrictFDerivAt f (L : E →L[ℝ] F) p` with `L : E ≃L[ℝ] F`. Uniform convergence of the derivatives is `TendstoUniformlyOn (fun k x => fderiv ℝ (h k) x) 0 atTop (ball p δ₀)`.
-- source:
--   General analysis lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemmas 7.2 and 7.3

import Mathlib

namespace FiniteEnergyPlane

open Metric Filter Topology Set
open scoped NNReal

/-- Let `E` be a real Banach space and `f : E → F` have a strict Fréchet derivative at `p` that is
a continuous linear isomorphism `L : E ≃L[ℝ] F`, with `f p = 0`. Let `hₖ : E → F` be differentiable
on a ball `B(p, δ₀)` with `hₖ p → 0` and `fderiv hₖ → 0` uniformly on that ball. Then there is
`δ > 0` such that `f + hₖ` is injective on `B(p, δ)` for all large `k`, and there are points
`xₖ → p` with `f xₖ + hₖ xₖ = 0` for all large `k`. -/
theorem exists_tendsto_zero_of_tendsto_fderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E ≃L[ℝ] F} {p : E} (hf : HasStrictFDerivAt f (L : E →L[ℝ] F) p)
    (hp : f p = 0) {h : ℕ → E → F} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hd : ∀ k, ∀ x ∈ ball p δ₀, DifferentiableAt ℝ (h k) x)
    (h0 : Tendsto (fun k => h k p) atTop (𝓝 0))
    (hD : TendstoUniformlyOn (fun k x => fderiv ℝ (h k) x) 0 atTop (ball p δ₀)) :
    ∃ δ > 0, (∀ᶠ k in atTop, InjOn (fun x => f x + h k x) (ball p δ)) ∧
      ∃ x : ℕ → E, Tendsto x atTop (𝓝 p) ∧ ∀ᶠ k in atTop, f (x k) + h k (x k) = 0 := by
  sorry

end FiniteEnergyPlane
