-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_sum_antisymm
-- name    : Formalism.FourierDecayAlt.P.Mx6.L3.sum_antisymm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:29:50.893187+00:00
-- url     : https://prove2.me/theorems/59e7ecb7-3373-494f-a2b9-b96117768f29
-- title:
--   L3: sum antisymm
-- statement:
--   The L3 construction uses the sum antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1230-L1239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1230-L1239

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L3
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)

theorem Formalism.FourierDecayAlt.P.Mx6.L3.sum_antisymm {M : Type*} [AddCommGroup M] [Module ℂ M] (I : Finset ℕ) (F : ℕ → ℕ → M)
    (h : ∀ i ∈ I, ∀ j ∈ I, F i j + F j i = 0) : ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by sorry
