-- Prove2me | Theorems.Thm_CauchyRiemannIndex_homotopy_lift_of_local_transport
-- name    : CauchyRiemannIndex.homotopy_lift_of_local_transport
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T16:49:23.332401+00:00
-- url     : https://prove2.me/theorems/c48f9463-4c74-4450-aa98-8a64ba801e27
-- title:
--   Homotopy lifting for matrix orbit maps with a continuous local transport
-- statement:
--   Let $\iota$ be a finite set, $S$ a submonoid of the real $\iota\times\iota$ matrices, $U\subseteq\mathbb R^\iota\times\mathbb R^\iota$ open, and $\tau:U\to S$ continuous with $\tau(x,y)\,x=y$ for $(x,y)\in U$ and $\tau(x,x)=\mathrm{Id}$ whenever $(x,x)\in U$. Let $H:[0,1]\times[0,1]\to\mathbb R^\iota$ be continuous with $(H(p),H(p))\in U$ for every $p$, let $e\in\mathbb R^\iota$, and let $\gamma:[0,1]\to S$ be continuous with $\gamma(t)e=H(0,t)$. Then there is a continuous $G:[0,1]\times[0,1]\to S$ with
--   $$G(0,t)=\gamma(t),\qquad G(s,t)\,e=H(s,t)\quad\text{for all }s,t,$$
--   and with $G(s,t)=\gamma(t)$ for all $s$ at every $t$ for which $s\mapsto H(s,t)$ is constant.
--
--   This is a homotopy lifting property for the orbit map $A\mapsto Ae$ on $S$: any homotopy of the orbit path $t\mapsto\gamma(t)e$ lifts to a homotopy of $\gamma$ in $S$, and the lift leaves $\gamma(t)$ fixed at those times where the given homotopy does not move. In particular homotopies relative to end points lift to homotopies relative to end points.
--
--   **Formalization Note.** Vectors are `ι → ℝ`, matrices `Matrix ι ι ℝ` acting by `*ᵥ`, and `S : Submonoid (Matrix ι ι ℝ)`. `τ` is a total function with `ContinuousOn τ U`; the hypotheses on `τ` are required only on `U`. $H$ and $G$ are continuous maps on `unitInterval × unitInterval`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (auxiliary fact for Theorem 3.34: the fundamental group of $\mathrm{Sp}(2n)$)

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- Homotopy lifting along `A ↦ A e` for a submonoid `S` of matrices that admits a continuous
local transport `τ` near the diagonal: a homotopy `H` of `t ↦ γ(t) e` lifts to a homotopy `G` in
`S` of `γ` with `G e = H`, constant in `s` wherever `H` is. -/
theorem homotopy_lift_of_local_transport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Submonoid (Matrix ι ι ℝ)) (U : Set ((ι → ℝ) × (ι → ℝ))) (hU : IsOpen U)
    (τ : (ι → ℝ) × (ι → ℝ) → Matrix ι ι ℝ) (hτc : ContinuousOn τ U)
    (hτS : ∀ p ∈ U, τ p ∈ S) (hτv : ∀ p ∈ U, τ p *ᵥ p.1 = p.2)
    (hτ1 : ∀ x, (x, x) ∈ U → τ (x, x) = 1)
    (H : C(unitInterval × unitInterval, ι → ℝ)) (hHU : ∀ p, (H p, H p) ∈ U) (e : ι → ℝ)
    (γ : C(unitInterval, Matrix ι ι ℝ)) (hγS : ∀ t, γ t ∈ S) (hγ : ∀ t, γ t *ᵥ e = H (0, t)) :
    ∃ G : C(unitInterval × unitInterval, Matrix ι ι ℝ), (∀ t, G (0, t) = γ t) ∧
      (∀ p, G p ∈ S) ∧ (∀ p, G p *ᵥ e = H p) ∧
      ∀ t, (∀ s, H (s, t) = H (0, t)) → ∀ s, G (s, t) = γ t := by sorry

end CauchyRiemannIndex
