-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_sum_eq_zero_of_anti
-- name    : Formalism.DegreeFormula.PPowSum.sum_eq_zero_of_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:52.005368+00:00
-- url     : https://prove2.me/theorems/b6e558c1-e048-4002-b992-4eff9ccee53f
-- title:
--   PPow Sum: sum eq zero of anti
-- statement:
--   The PPow Sum construction uses the sum eq zero of anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L106-L110

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

theorem Formalism.DegreeFormula.PPowSum.sum_eq_zero_of_anti {G : Type*} [Group G] [Fintype G] (ρ : G) (F : G → ℝ)
    (h : ∀ g, F (ρ * g) = -F g) : ∑ g, F g = 0 := by sorry
