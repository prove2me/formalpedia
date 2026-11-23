-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_idl_ne_zero
-- name    : Formalism.FourierDecayAlt.P.Jx2.idl_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:52.310115+00:00
-- url     : https://prove2.me/theorems/16ba6ccd-4eff-40a0-aacb-8539ba2006c2
-- title:
--   Jx2: idl ne zero
-- statement:
--   The Jx2 construction uses the idl ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L445-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L445-L454

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate

theorem Formalism.FourierDecayAlt.P.Jx2.idl_ne_zero (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (hg : 0 < g) : S6.idl E g k ν ≠ 0 := by sorry
