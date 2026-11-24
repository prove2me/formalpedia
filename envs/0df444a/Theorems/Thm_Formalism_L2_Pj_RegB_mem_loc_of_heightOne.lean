-- Prove2me | Theorems.Thm_Formalism_L2_Pj_RegB_mem_loc_of_heightOne
-- name    : Formalism.L2.Pj.RegB.mem_loc_of_heightOne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:35.333936+00:00
-- url     : https://prove2.me/theorems/2109b570-db2e-4392-8834-9549abfbc84b
-- title:
--   Reg B: mem loc of height One
-- statement:
--   The Reg B construction uses the mem loc of height One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegModelB.lean#L9-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegModelB.lean#L9-L153

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegHor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegKrull
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.RegB
open IsLocalRing ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal

theorem Formalism.L2.Pj.RegB.mem_loc_of_heightOne {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (qq : Ideal R) [hq : qq.IsPrime]
    (x : K) (hx : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p ≤ qq →
      ∃ a s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K a) :
    ∃ a s : R, s ∉ qq ∧ x * algebraMap R K s = algebraMap R K a := by sorry
