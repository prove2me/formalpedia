-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_Z_sum
-- name    : Formalism.DegreeFormula.PPowSum.Z_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:33.229612+00:00
-- url     : https://prove2.me/theorems/4fcaa416-e591-48d6-98d7-e8148b19a98c
-- title:
--   PPow Sum: Z sum
-- statement:
--   The PPow Sum construction uses the Z sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L161-L166

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

theorem Formalism.DegreeFormula.PPowSum.Z_sum {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} {α : Type*} (s : Finset α)
    (g : α → MvPolynomial (ι × Fin N) ℝ) (h : ∀ a ∈ s, ∀ P, degFl ι N (g a * P) = 0) :
    ∀ P, degFl ι N ((∑ a ∈ s, g a) * P) = 0 := by sorry
