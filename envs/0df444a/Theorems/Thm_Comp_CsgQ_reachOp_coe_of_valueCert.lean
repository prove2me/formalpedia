-- Prove2me | Theorems.Thm_Comp_CsgQ_reachOp_coe_of_valueCert
-- name    : Comp.CsgQ.reachOp_coe_of_valueCert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:27:34.419821+00:00
-- url     : https://prove2.me/theorems/4349ec26-f842-4d9b-a582-88a57b184604
-- title:
--   Csg Q: reach Op coe of value Cert
-- statement:
--   At a non-goal state, a value certificate on the rational stage game pins the operator's value
--       there. Stated about the real coercion, so the subtype never appears.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L187-L195
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L187-L195

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.reachOp_coe_of_valueCert (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) {s : S} {t : ℚ}
    {p : A1 → ℚ} {q : A2 → ℚ} (hs : ¬ goal s)
    (hc : (G.reachGameQ s v).ValueCert t p q) :
    ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((t : ℚ) : ℝ) := by sorry
