-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_sum_perm_rev
-- name    : Formalism.DegreeFormula.PFlagDeg.sum_perm_rev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:19.70446+00:00
-- url     : https://prove2.me/theorems/1aea3c29-b174-4a7d-b921-6c71d4347170
-- title:
--   PFlag Deg: sum perm rev
-- statement:
--   The PFlag Deg construction uses the sum perm rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L20-L25

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg

theorem Formalism.DegreeFormula.PFlagDeg.sum_perm_rev {N : ℕ} (s : Equiv.Perm (Fin N)) :
    ∑ i : Fin N, (N - 1 - ((s i : Fin N) : ℕ)) = ∑ i : Fin N, (i : ℕ) := by sorry
