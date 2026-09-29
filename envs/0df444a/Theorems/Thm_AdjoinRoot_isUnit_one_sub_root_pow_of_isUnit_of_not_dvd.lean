-- Prove2me | Theorems.Thm_AdjoinRoot_isUnit_one_sub_root_pow_of_isUnit_of_not_dvd
-- name    : AdjoinRoot.isUnit_one_sub_root_pow_of_isUnit_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/f14763a3-d83f-5170-be81-2ed27df784e1
-- title:
--   Units 1-x^j in 𝒪[X]/(Φ_m) when m is invertible
-- statement:
--   Let $\mathcal O$ be a commutative ring (in an arbitrary universe), let $m$ be a natural number whose image $(m:\mathcal O)$ under the canonical map $\mathbb N \to \mathcal O$ is a unit, and let $j$ be a natural number that is not divisible by $m$. Form the ring $\mathcal O[X]/(\Phi_m)$, where $\Phi_m$ is the $m$-th cyclotomic polynomial with coefficients in $\mathcal O$, and let $x$ denote the canonical root of $\Phi_m$ in that quotient, i.e. the class of $X$. The assertion is that $1 - x^{\,j}$ is a unit of $\mathcal O[X]/(\Phi_m)$. No hypothesis of connectedness, reducedness or nontriviality is placed on $\mathcal O$, and no primality or positivity hypothesis is placed on $m$ beyond what invertibility of $(m:\mathcal O)$ forces; for $j = 0$ the divisibility hypothesis $\neg\, m \mid j$ fails unless $m = 0$, in which case invertibility of $(0:\mathcal O)$ makes $\mathcal O$, and hence the quotient, trivial.
--
--   This is the statement that the class of $X$ in $\mathcal O[X]/(\Phi_m)$ is a primitive $m$-th root of unity in the strong sense required for étale descent along cyclotomic covers: not merely $x^m = 1$ with $x^j \ne 1$, but $1 - x^j$ invertible for all $j$ not divisible by $m$. It is used in the construction of cyclotomic Galois covers and of the associated tensor-product algebra isomorphism, and in the production of level structures on polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdjoinRoot_isUnit_one_sub_root_pow_of_isUnit_of_not_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

universe u

theorem AdjoinRoot.isUnit_one_sub_root_pow_of_isUnit_of_not_dvd
    (𝒪 : Type u) [CommRing 𝒪] (m : ℕ) (hm : IsUnit ((m : ℕ) : 𝒪)) (j : ℕ) (hj : ¬ m ∣ j) :
    IsUnit (1 - AdjoinRoot.root (cyclotomic m 𝒪) ^ j) := by sorry
