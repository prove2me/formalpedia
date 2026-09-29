-- Prove2me | Theorems.Thm_FamousTheorems_chsh_inequality_commutative
-- name    : FamousTheorems.chsh_inequality_commutative
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:10:01.247299+00:00
-- url     : https://prove2.me/theorems/c66488a6-3a3d-477b-a9d8-30bdf1a138a7
-- title:
--   The CHSH inequality
-- statement:
--   **The CHSH inequality.** Let $A_0,A_1,B_0,B_1$ be self-adjoint elements of a commutative star-ordered $\mathbb R$-algebra with $A_i^2=B_j^2=1$ and each $A_i$ commuting with each $B_j$. Then
--   $$A_0B_0+A_0B_1+A_1B_0-A_1B_1\le2.$$
--
--   Clauser, Horne, Shimony and Holt derived this form of Bell's inequality in 1969. In a classical local hidden-variable theory, where all observables commute, the correlation is at most $2$. Quantum mechanics allows values up to $2\sqrt2$ (Tsirelson's bound), and violations of the inequality have been confirmed experimentally.
--
--   **Formalization note.** Mathlib's `CHSH_inequality_of_comm`. `IsCHSHTuple A₀ A₁ B₀ B₁` bundles the conditions that each element is a self-adjoint involution and that each $A_i$ commutes with each $B_j$. The ring is commutative with a partial order compatible with the star structure (`StarOrderedRing`) and with scalar multiplication by $\mathbb R$ (`IsOrderedModule ℝ R`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CHSH_inequality_of_comm`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem chsh_inequality_commutative {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R] [Algebra ℝ R]
    [IsOrderedModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 := by sorry

end FamousTheorems
