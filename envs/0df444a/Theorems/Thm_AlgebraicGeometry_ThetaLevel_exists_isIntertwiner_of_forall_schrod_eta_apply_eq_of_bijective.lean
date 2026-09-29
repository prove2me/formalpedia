-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective
-- name    : AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/0abb61f5-74a2-5ade-ba3c-65e9e582dc58
-- title:
--   Intertwiner from an η-fixed vector generating the Schrödinger module
-- statement:
--   Fix $g$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ of nonzero entries, and a nonzero natural number $d$ with $\prod_i \delta_i = d$; write $H(\delta) = \prod_i \mathbb{Z}/\delta_i$ for `HH δ` and let `Heis δ d` be the set of triples $z = (z.a, z.h, z.k)$ with $z.a \in \mathbb{Z}/2d$ and $z.h, z.k \in H(\delta)$, with its group structure. Let $B$ be a commutative ring in which the image of $d$ is a unit, and let $\zeta, \omega \in B$ satisfy $\zeta^d = 1$, $1 - \zeta^j$ a unit for all $0 < j < d$, and $\omega^2 = \zeta$. Let $n$ be a natural number and $e : \mathrm{Fin}\,n \simeq H(\delta)$ an enumeration. Let $\gamma$ be an automorphism of the group `Heis δ d` lying in `Heis.Gam δ d`, i.e. fixing every central element $\mathrm{cen}\,a$. Here the Schrödinger operator `schrod δ d B ω z` on $B^{H(\delta)}$ is $\omega^{z.a}$ times multiplication by the character $h \mapsto \omega^{\langle z.k, h\rangle}$ followed by translation by $z.h$, and $\theta_x = (0,x,0)$, $\eta_k = (0,0,k)$. Assume $v \in B^{H(\delta)}$ satisfies `schrod δ d B ω (γ (Heis.eta k)) v = v` for every $k \in H(\delta)$, and that the $B$-linear map $c \mapsto \sum_{x \in H(\delta)} c(x)\,\cdot$ `schrod δ d B ω (γ (Heis.theta x)) v` from $B^{H(\delta)}$ to itself is bijective. Then there exists a matrix $U \in M_n(B)$ with `IsIntertwiner δ d B ω e γ U`, that is, $U$ is a unit and $U \cdot$ `schrodMat δ d B ω e z` $=$ `schrodMat δ d B ω e (γ z)` $\cdot U$ for every $z \in$ `Heis δ d`, where `schrodMat δ d B ω e z` has $(i,j)$ entry $\omega^{(z.a + \langle z.k, e(j)\rangle)}$ when $e(i) = e(j) + z.h$ and $0$ otherwise.
--
--   This is the existence half of the uniqueness-of-the-Schrödinger-representation mechanism: an automorphism of the finite Heisenberg group acting trivially on the centre is implemented by a conjugation on the standard model, provided one exhibits a vector invariant under the operators attached to the subgroup of $\eta_k$ whose $\theta$-translates form a basis. It is used by [`AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_mem_gam`](thm.html#AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_mem_gam), where such a vector is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d)
    (v : HH δ → B) (hv : ∀ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) v = v)
    (hbij : Function.Bijective fun c : HH δ → B => ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) v) :
    ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U := by sorry
