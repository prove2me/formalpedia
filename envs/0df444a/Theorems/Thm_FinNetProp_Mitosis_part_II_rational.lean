-- Prove2me | Theorems.Thm_FinNetProp_Mitosis_part_II_rational
-- name    : FinNetProp.Mitosis.part_II_rational
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:34.5181+00:00
-- url     : https://prove2.me/theorems/f9314e55-5eba-4fb2-9015-2d47db70d778
-- title:
--   Proof of Theorem 4.2, Part II, Cases A.4–A.5, pp. 2809–2810 — the basic axioms without continuity, and mitosis, force (2.1) when all liabilities are rational
-- statement:
--   Let $b$ be a bankruptcy rule satisfying claims boundedness (Axiom 3.1), limited liability (Axiom 3.2), priority of creditors (Axiom 3.3), impartiality (Axiom 3.5) and invariance to mitosis (Axiom 4.1). Let $F = (N, z, L)$ be a financial network all of whose liabilities $L_{ij}$ are rational numbers. Then $b(F)$ solves the system (2.1) for $F$:
--   $$b_{ij}(F) = \min\Big\{\Pi_{ij}\Big(z_i + \sum_{k \in N} b_{ki}(F)\Big),\ L_{ij}\Big\}, \qquad i, j \in N,$$
--   that is, $b(F) = p(F)$.
--
--   This is the rational case of Part (II) of the proof of Theorem 4.2; continuity is then used only to pass from rational to real liabilities.
--
--   **Formalization Note** Continuity is not a hypothesis: the page's argument for this case (Cases A.4, A.5(a), A.5(b)) does not use it, as the introduction of Appendix A states.
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, pp. 2809–2810, proof of Theorem 4.2, Part II, Cases A.4–A.5 ('We have shown that b(F) = p(F) when all liabilities in F are rational numbers.', p. 2810); Appendix A introduction, p. 2808

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

theorem part_II_rational (b : BankruptcyRule) (hcb : ClaimsBounded b)
    (hll : LimitedLiability b) (hpc : PriorityOfCreditors b) (himp : Impartial b)
    (hmit : InvariantToMitosis b) (F : FinNet) (hF : RationalLiabilities F) :
    IsPropSolution F (b F) := by sorry

end FinNetProp.Mitosis
