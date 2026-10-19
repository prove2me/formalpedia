-- Prove2me | Theorems.Thm_FinNetProp_Mitosis_part_II
-- name    : FinNetProp.Mitosis.part_II
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:42.073079+00:00
-- url     : https://prove2.me/theorems/6eaa3841-186a-4afb-ab41-54430062d1ee
-- title:
--   Proof of Theorem 4.2, Part II, pp. 2809–2810 — a bankruptcy rule satisfying the six axioms is the proportional rule
-- statement:
--   Let $b$ be a bankruptcy rule satisfying claims boundedness (Axiom 3.1), limited liability (Axiom 3.2), priority of creditors (Axiom 3.3), continuity (Axiom 3.4), impartiality (Axiom 3.5) and invariance to mitosis (Axiom 4.1). Then for every financial network $F = (N, z, L)$ the payment matrix $b(F)$ solves the system (2.1) for $F$:
--   $$b_{ij}(F) = \min\Big\{\Pi_{ij}\Big(z_i + \sum_{k \in N} b_{ki}(F)\Big),\ L_{ij}\Big\}, \qquad i, j \in N.$$
--   By uniqueness of the solution of (2.1), $b = p$.
--
--   This is the uniqueness half of Theorem 4.2.
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, pp. 2809–2810, Proof of Theorem 4.2, Part II

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

theorem part_II (b : BankruptcyRule) (hcb : ClaimsBounded b) (hll : LimitedLiability b)
    (hpc : PriorityOfCreditors b) (hcont : RuleContinuous b) (himp : Impartial b)
    (hmit : InvariantToMitosis b) :
    ∀ F : FinNet, IsPropSolution F (b F) := by sorry

end FinNetProp.Mitosis
