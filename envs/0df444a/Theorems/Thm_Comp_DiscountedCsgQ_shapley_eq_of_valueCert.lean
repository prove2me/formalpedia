-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_shapley_eq_of_valueCert
-- name    : Comp.DiscountedCsgQ.shapley_eq_of_valueCert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:34:12.110509+00:00
-- url     : https://prove2.me/theorems/3defa7df-8b51-4e7f-a951-c30a28711fa5
-- title:
--   Discounted Csg Q: shapley eq of value Cert
-- statement:
--   **The usable per-state step.** A value certificate on the rational stage game at `s` pins the
--       real Shapley operator's value there. Same conclusion as `Comp/Shapley.lean`'s
--       `shapley_eq_of_find`, but conditional on a `ValueCert` at literals -- which `norm_num` can
--       discharge -- rather than on the search having returned, which only `native_decide` could
--       establish.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L86-L92
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L86-L92

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate
set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.DiscountedCsgQ.shapley_eq_of_valueCert (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {v : S → ℚ} {s : S} {t : ℚ} {p : A1 → ℚ} {q : A2 → ℚ}
    (hc : (G.shapleyGameQ s v).ValueCert t p q) :
    (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s = ((t : ℚ) : ℝ) := by sorry
