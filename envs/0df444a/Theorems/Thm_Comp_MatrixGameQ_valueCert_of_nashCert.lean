-- Prove2me | Theorems.Thm_Comp_MatrixGameQ_valueCert_of_nashCert
-- name    : Comp.MatrixGameQ.valueCert_of_nashCert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:09:55.652975+00:00
-- url     : https://prove2.me/theorems/d2b9487d-0e41-49a6-8f1b-a3e3ad573f45
-- title:
--   Matrix Game Q: value Cert of nash Cert
-- statement:
--   **The zero-sum corollary.** A Nash certificate for the zero-sum bimatrix game is a value
--       certificate for the original matrix game, with the equilibrium payoff as the value. Note which
--       clauses are used: only the two *inequality* families, never the complementarity ones -- the
--       sandwich needs no more, as the module docstring explains.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L231-L240
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean#L231-L240

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ

theorem Comp.MatrixGameQ.valueCert_of_nashCert {G : MatrixGameQ I J} {p : I → ℚ} {q : J → ℚ}
    (h : G.toBimatrixQ.NashCert p q) :
    G.ValueCert (G.toBimatrixQ.colPayoff p q) p q := by sorry
