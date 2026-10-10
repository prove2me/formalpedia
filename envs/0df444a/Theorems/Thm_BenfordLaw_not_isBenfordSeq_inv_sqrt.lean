-- Prove2me | Theorems.Thm_BenfordLaw_not_isBenfordSeq_inv_sqrt
-- name    : BenfordLaw.not_isBenfordSeq_inv_sqrt
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:27.564849+00:00
-- url     : https://prove2.me/theorems/63ae574d-2b27-4bd7-9597-13b32a2d5c36
-- title:
--   Reciprocals and square roots of the naturals are not Benford
-- statement:
--   Neither the reciprocals $1/1, 1/2, 1/3,\dots$ nor the square roots $\sqrt1,\sqrt2,\sqrt3,\dots$ of the successive natural numbers satisfy Benford's law in base $10$: for each of the two sequences there is a digit $d \in\{1,\dots,9\}$ for which the relative frequency of leading digit $d$ among the first $N$ terms does not converge to $\log_{10}(1+1/d)$.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Distributions known to disobey Benford's law" ("The square roots and reciprocals of successive natural numbers do not obey this law", ref. Raimi 1976).

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem not_isBenfordSeq_inv_sqrt :
    ¬ IsBenfordSeq 10 (fun n => 1 / ((n : ℝ) + 1)) ∧
      ¬ IsBenfordSeq 10 (fun n => Real.sqrt ((n : ℝ) + 1)) := by sorry

end BenfordLaw
