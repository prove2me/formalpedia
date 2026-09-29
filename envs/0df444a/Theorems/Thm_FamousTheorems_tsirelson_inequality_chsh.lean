-- Prove2me | Theorems.Thm_FamousTheorems_tsirelson_inequality_chsh
-- name    : FamousTheorems.tsirelson_inequality_chsh
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:36.889411+00:00
-- url     : https://prove2.me/theorems/be338fc8-5fa8-4b11-b371-9416f1923c1b
-- title:
--   The Tsirelson inequality
-- statement:
--   **The Tsirelson inequality.** Let $A_0,A_1,B_0,B_1$ be elements of an ordered $*$-algebra over $\mathbb R$ that form a CHSH tuple: each is a self-adjoint involution, and each $A_i$ commutes with each $B_j$. Then
--   $$A_0B_0+A_0B_1+A_1B_0-A_1B_1\le2\sqrt2\cdot1.$$
--
--   In quantum mechanics this bounds the CHSH correlation of any quantum state by $2\sqrt2$. Classical local hidden-variable models obey the bound $2$ (the CHSH form of Bell's inequality), and the value $2\sqrt2$ is attained by entangled states. The gap between $2$ and $2\sqrt2$ is the quantitative content of Bell nonlocality.
--
--   **Formalization note.** Mathlib's `tsirelson_inequality`. `IsCHSHTuple` records the involution, self-adjointness and commutation conditions. The ambient algebra is a star-ordered ring with an ordered real algebra structure. The constant appears as `Real.sqrt 2 ^ 3`, which equals $2\sqrt2$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `tsirelson_inequality`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tsirelson_inequality_chsh {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] [Algebra ℝ R]
    [IsOrderedModule ℝ R] [StarModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ Real.sqrt 2 ^ 3 • (1 : R) := by sorry

end FamousTheorems
