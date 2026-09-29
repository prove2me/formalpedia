-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply
-- name    : AlgebraicGeometry.ThetaLevel.forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/5de78006-c889-5624-a318-dcc82979bcc5
-- title:
--   Unit-coordinate averaged vector is η-invariant with basis of θ-translates
-- statement:
--   Fix $g$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero, and a nonzero $d$ with $\prod_i \delta_i = d$; write $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring in which the image of $d$ is a unit, and let $\zeta,\omega \in B$ satisfy $\zeta^d = 1$, $1 - \zeta^j \in B^\times$ for all $0 < j < d$, and $\omega^2 = \zeta$; let $e : \mathrm{Fin}\,n \simeq H(\delta)$ be an enumeration of $H(\delta)$. On $B^{H(\delta)}$ the Schrödinger action `schrod` sends an element $z = (a,h,k)$ of the Heisenberg set `Heis` $\delta\,d$ (with $a \in \mathbb{Z}/2d$ and $h,k \in H(\delta)$) to $\omega^{a.\mathrm{val}}$ times multiplication by the character $x \mapsto \omega^{(\mathrm{pair}\,k\,x).\mathrm{val}}$ followed by precomposition with $x \mapsto x - h$; here $\theta_h = (0,h,0)$ and $\eta_k = (0,0,k)$. Let $\gamma$ be an automorphism of `Heis` $\delta\,d$ lying in the subgroup `Heis.Gam`, i.e. fixing `cen a` for every $a$. Put $v = \sum_{k \in H(\delta)} \mathrm{schrod}(\gamma(\eta_k))\,\delta_{y_0}$ for some $y_0 \in H(\delta)$, where $\delta_{y_0}$ is the indicator of $y_0$, and assume the $y_0$-coordinate $v(y_0)$ is a unit in $B$. Then $\mathrm{schrod}(\gamma(\eta_k))\,v = v$ for every $k \in H(\delta)$, and the map $B^{H(\delta)} \to B^{H(\delta)}$, $c \mapsto \sum_{x \in H(\delta)} c(x)\cdot \mathrm{schrod}(\gamma(\theta_x))\,v$, is bijective.
--
--   This is the weight-vector and weight-basis step for the Schrödinger representation of the Heisenberg group twisted by an automorphism fixing the centre: averaging over the $\eta$-part produces a vector invariant under all $\eta_k$ whose $\theta$-translates form a $B$-basis of $B^{H(\delta)}$. It is used by [`AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_mem_gam`](thm.html#AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_mem_gam) to produce an intertwining operator between the Schrödinger representation and its twist by $\gamma$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d)
    (y₀ : HH δ) (hy₀ : IsUnit ((∑ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (Pi.single y₀ 1)) y₀)) :
    (∀ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) =
        ∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) ∧
      Function.Bijective fun c : HH δ → B =>
        ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) (∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) := by sorry
