-- Prove2me | Theorems.Thm_Comp_MatrixGameQ_value_eq_of_valueCert
-- name    : Comp.MatrixGameQ.value_eq_of_valueCert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:44:13.230082+00:00
-- url     : https://prove2.me/theorems/e0be48d4-8434-4801-9fa1-45df20449f34
-- title:
--   Matrix Game Q: value eq of value Cert
-- statement:
--   **The payoff of this file.** A value certificate pins the real-valued game value exactly: no
--       approximation, no error term. The row inequalities put `t` in `rowLPFeasible`, so
--       `value ≤ t` by `value_isLeast_rowLPFeasible`; the column inequalities put `t` in
--       `colLPFeasible`, so `t ≤ value` by `value_isGreatest_colLPFeasible`; `le_antisymm` finishes.
--
--       All the mathematics is in those two theorems, which is why this proof is bookkeeping: cast the
--       rational witnesses into `ℝ`, and cast the rational inequalities across the finite sums.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L141-L154
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L141-L154

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ

theorem Comp.MatrixGameQ.value_eq_of_valueCert {G : MatrixGameQ I J} {t : ℚ} {p : I → ℚ} {q : J → ℚ}
    (h : G.ValueCert t p q) : G.toMatrixGame.value = ((t : ℚ) : ℝ) := by sorry
