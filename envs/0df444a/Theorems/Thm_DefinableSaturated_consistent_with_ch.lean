-- Prove2me | Theorems.Thm_DefinableSaturated_consistent_with_ch
-- name    : DefinableSaturated.consistent_with_ch
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T22:49:17.811795+00:00
-- url     : https://prove2.me/theorems/8e9adb68-9f83-4fdd-92a7-d400b7345e39
-- title:
--   Consistency of CH with a definable saturated arithmetic isomorphism type having no OD copy
-- statement:
--   This is the headline relative-consistency result of the definable-saturated development.
--
--   Write $\sigma_{\mathrm{CH}}$ for the first-order sentence asserting that the continuum hypothesis holds, that a countably saturated elementary extension of the natural-number arithmetic structure $(\mathbb N,0,1,+,\times)$ of cardinality $\aleph_1$ exists, that any two such presentations are isomorphic, and that no such presentation on any set-sized domain is ordinal definable. Then
--   $$\big(\mathrm{ZFC}\cup\{\sigma_{\mathrm{CH}}\}\big)\ \text{is satisfiable,}$$
--   i.e. some first-order model of ZFC satisfies $\sigma_{\mathrm{CH}}$.
--
--   The theorem asserts the existence of a single model of set theory in which the isomorphism type of the saturated arithmetic model is pinned down without parameters yet has no ordinal-definable representative, alongside CH. It is a consistency statement in Lean's metatheory: it does **not** assert that ZFC proves its own consistency.
--
--   **Formalization Note.** Arithmetic, countability, saturation, $\aleph_1$, and ordinal definability are all interpreted inside the first-order model via explicit formula codes; `IsSatisfiable` is `FirstOrder.Language.Theory.IsSatisfiable`.
-- source:
--   https://github.com/elliotglazer/definable-saturated/blob/6d4822c80dd6/DefinableSaturated/Challenge.lean#L745-L748

import Mathlib.ModelTheory.Satisfiability
import Definitions.Def_definable_saturated_arithmetic

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace DefinableSaturated
theorem consistent_with_ch :
    (Erdos501.FOL.ZFC ∪
      {Scotts.FOL.ScottStatement.scottCHSentence}).IsSatisfiable := by
  sorry
end DefinableSaturated
