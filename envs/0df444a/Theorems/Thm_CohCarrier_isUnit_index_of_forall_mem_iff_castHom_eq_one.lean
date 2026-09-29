-- Prove2me | Theorems.Thm_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one
-- name    : CohCarrier.isUnit_index_of_forall_mem_iff_castHom_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/7b8c5df1-4152-5947-990f-1fc544b9b5f5
-- title:
--   Index of the mod-r congruence subgroup is a unit
-- statement:
--   Let $\mathcal O$ be a commutative local ring, $p$ a prime with the image of $p$ in $\mathcal O$ lying in the maximal ideal of $\mathcal O$, and let $N$ and $r$ be natural numbers with $N$ nonzero, with $r$ prime, with $p \nmid r-1$, and with $N r$ nonzero. Let $H_0$ be a subgroup of $(\mathbb Z/N r)^\times$ which is assumed to consist of exactly those units $v$ whose image under the reduction map $\mathbb Z/N r \to \mathbb Z/r$ (coming from $r \mid N r$) equals $1$; that is, $v \in H_0$ if and only if $v \equiv 1 \pmod r$. The conclusion is that the natural number $[(\mathbb Z/N r)^\times : H_0]$, viewed in $\mathcal O$ via the canonical map $\mathbb N \to \mathcal O$, is a unit of $\mathcal O$. Note that the congruence condition is imposed on the underlying element of $\mathbb Z/N r$, not on the unit, which is equivalent since the reduction of units is computed from the reduction of ring elements.
--
--   This is the elementary numerical input behind the choice of Taylor–Wiles auxiliary primes $r \not\equiv 1 \pmod p$: for such $r$ the index of the mod-$r$ congruence subgroup of $(\mathbb Z/Nr)^\times$ is invertible in the coefficient ring, so averaging or trace arguments over the corresponding quotient group are available. It is used in the construction and comparison of corner submodules at level $N r$ versus level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one.lean

import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.FieldTheory.Finite.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem CohCarrier.isUnit_index_of_forall_mem_iff_castHom_eq_one
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (N r : ℕ) [NeZero N] (hr : r.Prime) (hr1 : ¬ p ∣ r - 1) [NeZero (N * r)]
    (H₀ : Subgroup (ZMod (N * r))ˣ)
    (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1) :
    IsUnit ((H₀.index : ℕ) : 𝒪) := by sorry
