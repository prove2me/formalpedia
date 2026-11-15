-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_fromBlocks_last_covariance_system
-- name    : AppliedSDE.SarkkaSolin.ar1_fromBlocks_last_covariance_system
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:48:32.78623+00:00
-- url     : https://prove2.me/theorems/877aa9f9-5dc0-458f-9073-3a3487eebb69
-- title:
--   True AR1 covariance inverse system in Schur-block form with appended state covariance rhs
-- statement:
--   The inverse of the noisy AR1 covariance matrix acting on the final-state prior covariance vector solves the exact appended Schur-block system, with old-coordinate right-hand side equal to a times the previous last prior-covariance row and final-coordinate right-hand side V. Supports the Kalman variance induction step.
-- source:
--   Sarkka and Solin (2019), AR1/OU Gaussian-process batch versus Kalman identity. Reuse the Proved full covariance fromBlocks inverse system and cross-covariance scaling.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_fromBlocks_last_covariance_system
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r) :
    let e : (Fin (n + 1) ⊕ Fin 1) ≃ Fin (n + 2) := finSumFinEquiv
    let Cnew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      (Matrix.of fun i j => V * a ^ Nat.dist i.val j.val) +
        r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    let Cold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      (Matrix.of fun i j => V * a ^ Nat.dist i.val j.val) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    let B : Matrix (Fin (n + 1)) (Fin 1) ℝ :=
      fun i _ => V * a ^ (n + 1 - i.val)
    let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V + r
    let kold : Fin (n + 1) -> ℝ :=
      fun i => V * a ^ Nat.dist n i.val
    let knew : Fin (n + 2) -> ℝ :=
      fun j => V * a ^ Nat.dist (n + 1) j.val
    let z := Cnew⁻¹ |>.mulVec knew
    (Matrix.fromBlocks Cold B B.transpose D).mulVec (z ∘ e) =
      Sum.elim (a • kold) (fun _ : Fin 1 => V) := by
  sorry
