-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_degFl_C_mul
-- name    : Formalism.DegreeFormula.PPowSum.degFl_C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:24.259735+00:00
-- url     : https://prove2.me/theorems/8d5a0700-b6ae-4317-83f0-83841cdd2fd2
-- title:
--   PPow Sum: deg Fl C mul
-- statement:
--   The PPow Sum construction uses the deg Fl C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L13-L16

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

theorem Formalism.DegreeFormula.PPowSum.degFl_C_mul {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (c : ℝ) (P : MvPolynomial (ι × Fin N) ℝ) :
    degFl ι N (C c * P) = c * degFl ι N P := by sorry
