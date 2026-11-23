-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Dual_alg
-- name    : Formalism.FourierDecayAlt.P.Dual.alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:05.797485+00:00
-- url     : https://prove2.me/theorems/1335c481-77ed-4cdb-bd14-f39db690a9d6
-- title:
--   Dual: alg
-- statement:
--   The Dual construction uses the alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualIdealInclusion.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualIdealInclusion.lean#L7-L18

import Definitions.Def_Formalism_HermitianCurvature_StatementL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dual
open NumberField FractionalIdeal

theorem Formalism.FourierDecayAlt.P.Dual.alg {E : Type} [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hdd : dd ≠ 0) (ν g : ℤ) (hg : g ≠ 0) :
    spanSingleton _ (g : E) * (dd⁻¹ * (dd ^ ν * spanSingleton _ ((g : E) ^ 2))⁻¹) =
      dd ^ (-(ν + 1)) * spanSingleton _ ((g : E)⁻¹) := by sorry
