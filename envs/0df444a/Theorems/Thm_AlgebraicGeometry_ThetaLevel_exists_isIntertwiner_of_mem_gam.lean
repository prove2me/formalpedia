-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_mem_gam
-- name    : AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_mem_gam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/75c8ceea-f3e7-5c21-8fdf-f0e77bc76ebd
-- title:
--   Existence of intertwiners for centre-fixing Heisenberg automorphisms
-- statement:
--   Fix $g$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta i$ nonzero, and a nonzero natural number $d$ with $\prod_i \delta_i = d$; write $HH\,\delta$ for the finite abelian group $\prod_i \mathbb{Z}/\delta_i$ and $\mathrm{Heis}\,\delta\,d$ for the type of triples $(a,h,k)$ with $a \in \mathbb{Z}/2d$ and $h,k \in HH\,\delta$. Let $B$ be a commutative ring in which the image of $d$ is a unit, and let $\zeta,\omega \in B$ satisfy $\zeta^d = 1$, $1 - \zeta^j \in B^\times$ for all $0 < j < d$, and $\omega^2 = \zeta$. Let $e : \mathrm{Fin}\,n \simeq HH\,\delta$ be an enumeration of $HH\,\delta$, and let $\gamma$ be a multiplicative automorphism of $\mathrm{Heis}\,\delta\,d$ lying in `Heis.Gam δ d`, i.e. fixing every central element `cen a`. The conclusion asserts the existence of a matrix $U \in M_{n}(B)$ which is a unit in the matrix ring and satisfies $U \cdot \mathrm{schrodMat}(z) = \mathrm{schrodMat}(\gamma z) \cdot U$ for all $z \in \mathrm{Heis}\,\delta\,d$, where $\mathrm{schrodMat}(z)$ is the matrix whose $(i,j)$ entry is `omegaPow d B ω (z.a + pair δ d z.k (e j))` when $e\,i = e\,j + z.h$ and $0$ otherwise; that is, $U$ is an invertible intertwiner between the Schrödinger-type representation and its $\gamma$-twist.
--
--   This is the global, matrix-valued form over the base ring $B$ of the Stone–von Neumann–Mackey uniqueness statement for the finite Heisenberg group, as in Mumford's analysis of the theta group: the Schrödinger representation is rigid enough that any automorphism fixing the centre pointwise is implemented by an invertible conjugation. It is used in the construction of the theta level structure torsor, being cited in the existence of a free transitive theta-adapted finite group action and in the comparison of reframings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_mem_gam.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_mem_gam
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d) :
    ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U := by sorry
