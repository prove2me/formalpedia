-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_periodic_family_of_transition
-- name    : FiniteEnergyPlane.exists_periodic_family_of_transition
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T13:52:12.325683+00:00
-- url     : https://prove2.me/theorems/a8ccc1f6-750f-53ea-90fb-724a02fa2f12
-- title:
--   Closing up a family of maps with a transition to a periodic family
-- statement:
--   Let $E$ be a real normed space, $L,\delta,\eta>0$, $l\ge1$, and let $U:\mathbb{R}\times\mathbb{C}\to E$ be $C^l$ on $(-\delta,L+\delta)\times\mathbb{C}$. Suppose $\beta,c:\mathbb{R}\to\mathbb{R}$ and $A,B:\mathbb{R}\to\mathbb{C}$ are $C^l$ on $(-\eta,\eta)$ with $\beta(0)=L$, and for $|s|<\eta$ let $\beta(s)\in(-\delta,L+\delta)$, $\beta'(s)>0$, $A(s)\ne0$ and $$U(s,z)=e^{2c(s)}\,U(\beta(s),A(s)z+B(s))\qquad(z\in\mathbb{C}).$$ Then there are a $C^l$ map $W:\mathbb{R}\times\mathbb{C}\to E$, $1$-periodic in the first variable, and functions $\kappa,b,a,d$ such that $$W(\theta,z)=e^{2b(\theta-n)}\,U(\kappa(\theta-n),a(\theta-n)z+d(\theta-n))$$ whenever $n\in\mathbb{Z}$ and $-\tfrac13<\theta-n<1$. Here $\kappa,a,d$ are $C^l$ on $(-1,2)$, $\kappa(0)=0$, $\kappa(1)=L$, and on $(-1,2)$ one has $\kappa\in(-\delta,L+\delta)$, $\kappa'>0$, $a\neq0$.
--
--   Used to turn an interval family of pages whose end leaves agree into a circle family; it does not involve contact geometry.
--
--   **Formalization Note** Functions are total; the assertions concern only the stated intervals.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.2.2

import Mathlib

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

/-- Closing up a family of maps with a transition. Let `U` be a `C^l` family (`l ≥ 1`) on
`(-δ, L + δ) × ℂ` with values in a normed space, and for `|s| < η` let
`U(s, z) = e^{2 c(s)} U(β(s), A(s) z + B(s))` with `C^l` functions `β, c, A, B` such that `β(0) = L`,
`β' > 0` and `A ≠ 0`. Then there is a `C^l` family `W` on `ℝ × ℂ`, `1`-periodic in the first variable,
with `W(θ, z) = e^{2 b(t)} U(κ(t), a(t) z + d(t))`, `t = θ - n`, whenever `n ∈ ℤ` and
`-1/3 < θ - n < 1`. Here `κ, a, d` are `C^l` on `(-1, 2)`, `κ(0) = 0`, `κ(1) = L`, and on `(-1, 2)`
`κ` takes values in `(-δ, L + δ)`, `κ' > 0` and `a ≠ 0`. -/
theorem exists_periodic_family_of_transition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (l : ℕ) (hl : 1 ≤ l) (L δ η : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hη : 0 < η)
    (U : ℝ × ℂ → E) (hU : ContDiffOn ℝ l U (Set.Ioo (-δ) (L + δ) ×ˢ Set.univ))
    (β c : ℝ → ℝ) (A B : ℝ → ℂ) (hβ : ContDiffOn ℝ l β (ball 0 η))
    (hc : ContDiffOn ℝ l c (ball 0 η)) (hA : ContDiffOn ℝ l A (ball 0 η))
    (hB : ContDiffOn ℝ l B (ball 0 η)) (hβ0 : β 0 = L)
    (hβI : ∀ s ∈ ball (0 : ℝ) η, β s ∈ Set.Ioo (-δ) (L + δ))
    (hβ' : ∀ s ∈ ball (0 : ℝ) η, 0 < deriv β s) (hA0 : ∀ s ∈ ball (0 : ℝ) η, A s ≠ 0)
    (hUβ : ∀ s ∈ ball (0 : ℝ) η, ∀ z,
      U (s, z) = Real.exp (2 * c s) • U (β s, A s * z + B s)) :
    ∃ (W : ℝ × ℂ → E) (κ b : ℝ → ℝ) (a d : ℝ → ℂ), ContDiff ℝ l W ∧
      (∀ θ z, W (θ + 1, z) = W (θ, z)) ∧
      ContDiffOn ℝ l κ (Set.Ioo (-1) 2) ∧ ContDiffOn ℝ l a (Set.Ioo (-1) 2) ∧
      ContDiffOn ℝ l d (Set.Ioo (-1) 2) ∧ κ 0 = 0 ∧ κ 1 = L ∧
      (∀ θ ∈ Set.Ioo (-1 : ℝ) 2, κ θ ∈ Set.Ioo (-δ) (L + δ) ∧ 0 < deriv κ θ ∧ a θ ≠ 0) ∧
      ∀ (n : ℤ) (θ : ℝ), θ - n ∈ Set.Ioo (-1 / 3 : ℝ) 1 → ∀ z,
        W (θ, z) = Real.exp (2 * b (θ - n)) • U (κ (θ - n), a (θ - n) * z + d (θ - n)) := by
  sorry

end FiniteEnergyPlane
