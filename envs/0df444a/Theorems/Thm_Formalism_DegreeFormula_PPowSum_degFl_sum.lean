-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_degFl_sum
-- name    : Formalism.DegreeFormula.PPowSum.degFl_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:39.907323+00:00
-- url     : https://prove2.me/theorems/685198eb-6278-4fe4-9656-0f7187515841
-- title:
--   PPow Sum: deg Fl sum
-- statement:
--   The PPow Sum construction uses the deg Fl sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L22-L28

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula

theorem Formalism.DegreeFormula.PPowSum.degFl_sum {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} {α : Type*} (s : Finset α)
    (f : α → MvPolynomial (ι × Fin N) ℝ) :
    degFl ι N (∑ a ∈ s, f a) = ∑ a ∈ s, degFl ι N (f a) := by sorry
