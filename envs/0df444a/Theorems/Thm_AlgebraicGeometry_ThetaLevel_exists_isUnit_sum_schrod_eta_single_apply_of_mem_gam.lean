-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam
-- name    : AlgebraicGeometry.ThetaLevel.exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/adae624b-36a9-56be-bd6b-2e8fa01e14ed
-- title:
--   A unit coordinate for the η-averaged delta vector
-- statement:
--   Fix $g \in \mathbb{N}$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta i$ nonzero, and $d \in \mathbb{N}$ nonzero with $\prod_i \delta i = d$; write $H(\delta) = \prod_i \mathbb{Z}/\delta i$ (`HH`). Let $B$ be a commutative ring in which the image of $d$ is a unit, and let $\zeta, \omega \in B$ satisfy $\zeta^d = 1$, $1 - \zeta^{j}$ a unit of $B$ for every $j$ with $0 < j < d$, and $\omega^2 = \zeta$. Let $n \in \mathbb{N}$ and $e : \mathrm{Fin}\,n \simeq H(\delta)$ be an enumeration of $H(\delta)$. Let $\gamma$ be a multiplicative automorphism of the Heisenberg group `Heis` $\delta\,d$, whose elements are triples $(a,h,k)$ with $a \in \mathbb{Z}/2d$ and $h,k \in H(\delta)$, and assume $\gamma$ lies in `Heis.Gam` $\delta\,d$, i.e. $\gamma(\mathrm{cen}\,a) = \mathrm{cen}\,a$ for all $a$. For $z = (a,h,k)$, the operator `schrod` acts on $B$-valued functions on $H(\delta)$ by $(\mathrm{schrod}\,z\,f)(x) = \omega^{a.\mathrm{val}}\,\omega^{(\mathrm{pair}\,\delta\,d\,k\,(x-h)).\mathrm{val}}\,f(x-h)$, with `pair` the pairing of the definition module. The assertion: there exists $y_0 \in H(\delta)$ such that the value at $y_0$ of $\sum_{k \in H(\delta)} \mathrm{schrod}\,\delta\,d\,B\,\omega\,(\gamma(\eta_k))$ applied to the indicator function $\mathrm{Pi.single}\,y_0\,1$ is a unit of $B$, where $\eta_k = (0,0,k)$.
--
--   This is the unimodularity step in the comparison of the Schrödinger representation of the Heisenberg group $\mathrm{Heis}(\delta,d)$ with its twist by an automorphism fixing the centre: averaging the twisted operators over the subgroup $\{\eta_k\}$ produces a vector one of whose coordinates is invertible. It is used by [`AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_mem_gam`](thm.html#AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_mem_gam) to construct an intertwiner for such $\gamma$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d)
    :
    ∃ y₀ : HH δ, IsUnit ((∑ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (Pi.single y₀ 1)) y₀) := by sorry
