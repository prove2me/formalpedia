-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_coeff_Xpow_mul
-- name    : Formalism.DegreeFormula.PPowSum.coeff_Xpow_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:11.057847+00:00
-- url     : https://prove2.me/theorems/6bbbad11-93bb-4e62-92ae-b00ac7b709e1
-- title:
--   PPow Sum: coeff Xpow mul
-- statement:
--   The PPow Sum construction uses the coeff Xpow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L55-L61

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

theorem Formalism.DegreeFormula.PPowSum.coeff_Xpow_mul {ι : Type} [Fintype ι] {N : ℕ} (x : ι × Fin N) (k : ℕ)
    (m : (ι × Fin N) →₀ ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    (X x ^ k * P).coeff m = if k ≤ m x then P.coeff (m - Finsupp.single x k) else 0 := by sorry
