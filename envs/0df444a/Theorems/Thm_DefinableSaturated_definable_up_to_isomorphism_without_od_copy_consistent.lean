-- Prove2me | Theorems.Thm_DefinableSaturated_definable_up_to_isomorphism_without_od_copy_consistent
-- name    : DefinableSaturated.definable_up_to_isomorphism_without_od_copy_consistent
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T22:49:40.40616+00:00
-- url     : https://prove2.me/theorems/98382bcb-b0f5-4ea0-b75f-baf63feb5507
-- title:
--   Definability up to isomorphism without an ordinal-definable copy is consistent (MathOverflow 382009)
-- statement:
--   This is the direct negative answer to [MathOverflow 382009](https://mathoverflow.net/questions/382009/definability-up-to-isomorphism-versus-definability-of-an-isomorphic-copy).
--
--   Write $\sigma$ for the first-order sentence asserting that a countably saturated elementary extension of $(\mathbb N,0,1,+,\times)$ of cardinality $\aleph_1$ exists, that any two such presentations are isomorphic, and that no such presentation on any set-sized domain is ordinal definable. Then
--   $$\big(\mathrm{ZFC}\cup\{\sigma\}\big)\ \text{is satisfiable.}$$
--
--   Thus it is consistent with ZFC that a parameter-free definable nonempty class of mutually isomorphic set-sized structures has no ordinal-definable member: definability up to isomorphism does not yield a definable isomorphic copy. Compared with the CH version, the CH conjunct is dropped; the statement follows from it by omitting that conjunct.
--
--   **Formalization Note.** This is a `Theory.IsSatisfiable` assertion about an explicit first-order theory, interpreted inside a model of set theory; it is not a claim that ZFC proves its own consistency.
-- source:
--   https://github.com/elliotglazer/definable-saturated/blob/6d4822c80dd6/DefinableSaturated/Challenge.lean#L753-L756

import Mathlib.ModelTheory.Satisfiability
import Definitions.Def_definable_saturated_arithmetic

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace DefinableSaturated
theorem definable_up_to_isomorphism_without_od_copy_consistent :
    (Erdos501.FOL.ZFC ∪
      {Scotts.FOL.ScottStatement.scottSentence}).IsSatisfiable := by
  sorry
end DefinableSaturated
