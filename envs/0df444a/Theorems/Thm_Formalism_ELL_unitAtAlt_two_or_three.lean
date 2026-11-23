-- Prove2me | Theorems.Thm_Formalism_ELL_unitAtAlt_two_or_three
-- name    : Formalism.ELL.unitAtAlt.two_or_three
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:39.427351+00:00
-- url     : https://prove2.me/theorems/d3784bf4-030e-4f32-b580-9809e248935f
-- title:
--   unit At Alt: two or three
-- statement:
--   The unit At Alt construction uses the two or three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ModelUnitOf.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ModelUnitOf.lean#L9-L26

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ModelUnitOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.ELL Formalism.ELL.unitAtAlt
open Formalism.ELL

theorem Formalism.ELL.unitAtAlt.two_or_three {K : Type u} [NormedField K] [IsUltrametricDist K] :
    ‖(2 : K)‖ = 1 ∨ ‖(3 : K)‖ = 1 := by sorry
