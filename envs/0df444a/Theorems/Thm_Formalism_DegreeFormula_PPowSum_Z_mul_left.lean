-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_Z_mul_left
-- name    : Formalism.DegreeFormula.PPowSum.Z_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:26.686271+00:00
-- url     : https://prove2.me/theorems/8fbd62ec-d7eb-4af0-b201-c96639f66b03
-- title:
--   PPow Sum: Z mul left
-- statement:
--   The PPow Sum construction uses the Z mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L154-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L154-L159

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

theorem Formalism.DegreeFormula.PPowSum.Z_mul_left {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} {Q : MvPolynomial (ι × Fin N) ℝ}
    (hQ : ∀ P, degFl ι N (Q * P) = 0) (R : MvPolynomial (ι × Fin N) ℝ) :
    ∀ P, degFl ι N ((R * Q) * P) = 0 := by sorry
