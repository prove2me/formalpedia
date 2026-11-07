-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_problemPM_instance
-- name    : AaronsonAmbainis.Bridge.problemPM_instance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:28:45.873197+00:00
-- url     : https://prove2.me/theorems/99f85fee-1885-4eb3-9638-08839d9915c3
-- title:
--   Bridge: problem PM instance
-- statement:
--   **Non-vacuity of `ExplicitBoundPM`.** For `p = X₀` in one variable on `{-1,1}` (`true ↦ 1`,
--   `false ↦ -1`): total degree at most `1`, bounded by `1`, variance exactly `1`, influence exactly
--   `1`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L109-L145
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L109-L145

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.problemPM_instance :
    (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ).totalDegree ≤ 1 ∧
    (∀ Y : Fin 1 → Bool,
      |MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else -1)
          (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)| ≤ 1) ∧
    (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else -1)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - (∑ Z : Fin 1 → Bool, MvPolynomial.eval (fun i => if Z i then (1 : ℝ) else -1)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) / 2 ^ 1) ^ 2) / 2 ^ 1 = 1 ∧
    (∑ Y : Fin 1 → Bool,
        ((MvPolynomial.eval (fun k => if Y k then (1 : ℝ) else -1)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - MvPolynomial.eval (fun k => if Function.update Y 0 (!Y 0) k then (1 : ℝ) else -1)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) / 2) ^ 2) / 2 ^ 1 = 1 := by sorry
