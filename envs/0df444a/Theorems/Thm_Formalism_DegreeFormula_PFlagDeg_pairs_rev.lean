-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_pairs_rev
-- name    : Formalism.DegreeFormula.PFlagDeg.pairs_rev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:13.621432+00:00
-- url     : https://prove2.me/theorems/22a3e2d5-3d95-4f21-a661-e3249f463a0f
-- title:
--   PFlag Deg: pairs rev
-- statement:
--   The PFlag Deg construction uses the pairs rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L105-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L105-L120

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

theorem Formalism.DegreeFormula.PFlagDeg.pairs_rev {N : ℕ} (v : Fin N → ℝ) :
    ∏ i : Fin N, ∏ k : Fin N, (if i < k then v i - v k else 1) =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev j) - v (Fin.rev i)) := by sorry
