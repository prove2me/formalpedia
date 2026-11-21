-- Prove2me | Theorems.Thm_Corless_Dv_hyb_step
-- name    : Corless.Dv_hyb_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:45.654374+00:00
-- url     : https://prove2.me/theorems/841c6c19-65e6-468e-bcec-1cebee203658
-- title:
--   Corless: Dv hyb step
-- statement:
--   Changing the weight of edge `j` changes `D` by `(new - old) · X · D(left) · D(right)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L27-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L27-L45

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.Dv_hyb_step (s t : ℕ → ℤ) (j m : ℕ) :
    Dv (hyb s t (j + 1)) (j + m + 2) - Dv (hyb s t j) (j + m + 2)
      = C (s j - t j) * X * Dv (hyb s t j) j * Dv (fun i => hyb s t j (i + j + 2)) m := by sorry
