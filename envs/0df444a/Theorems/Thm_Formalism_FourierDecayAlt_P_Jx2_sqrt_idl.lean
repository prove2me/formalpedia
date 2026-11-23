-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_sqrt_idl
-- name    : Formalism.FourierDecayAlt.P.Jx2.sqrt_idl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:20.41886+00:00
-- url     : https://prove2.me/theorems/b66e360e-b11e-47a3-8c42-228e139c0d24
-- title:
--   Jx2: sqrt idl
-- statement:
--   The Jx2 construction uses the sqrt idl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L456-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L456-L460

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

theorem Formalism.FourierDecayAlt.P.Jx2.sqrt_idl (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (μ : ℤ)
    (hg : 0 < g) : √(FractionalIdeal.absNorm (S6.idl E g (-1) (-μ)) : ℝ) =
      (((g : ℝ) * S6.rd E ^ μ) ^ S6.deg E)⁻¹ := by sorry
