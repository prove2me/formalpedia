-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_conj6_instance
-- name    : AaronsonAmbainis.Bridge.conj6_instance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:38.5492+00:00
-- url     : https://prove2.me/theorems/546375ca-3d66-4c7b-977e-4108cc87c2ec
-- title:
--   Bridge: conj6 instance
-- statement:
--   **Non-vacuity of `ExplicitBound` and `PrintedConjecture`.** For `p = X₀` in one variable: total
--   degree at most `1`, values in `[0,1]` on the cube, variance exactly `1/4`, and the influence of
--   the variable (normalisation of arXiv:0911.0996) exactly `1`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L80-L104
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L80-L104

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.conj6_instance :
    (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ).totalDegree ≤ 1 ∧
    (∀ Y : Fin 1 → Bool,
      0 ≤ MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) ∧
        MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) ≤ 1) ∧
    (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - (∑ Z : Fin 1 → Bool, MvPolynomial.eval (fun i => if Z i then (1 : ℝ) else 0)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) / 2 ^ 1) ^ 2) / 2 ^ 1 = 1 / 4 ∧
    (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun k => if Y k then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - MvPolynomial.eval (fun k => if Function.update Y 0 (!Y 0) k then (1 : ℝ) else 0)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) ^ 2) / 2 ^ 1 = 1 := by sorry
