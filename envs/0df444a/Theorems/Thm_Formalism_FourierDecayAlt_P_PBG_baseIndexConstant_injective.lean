-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_baseIndexConstant_injective
-- name    : Formalism.FourierDecayAlt.P.PBG.baseIndexConstant_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:56:54.438632+00:00
-- url     : https://prove2.me/theorems/683e9746-4b94-55a1-ae25-2d03ab998f69
-- title:
--   PBG: base Index Constant injective
-- statement:
--   The PBG construction uses the base Index Constant injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L25-L30

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem Formalism.FourierDecayAlt.P.PBG.baseIndexConstant_injective {a b : Fin (2 * r + k + 1)} : c0 (k := k) a = c0 b ↔ a = b := by sorry
