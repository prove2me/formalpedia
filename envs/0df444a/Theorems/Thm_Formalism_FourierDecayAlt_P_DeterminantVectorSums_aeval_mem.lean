-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_aeval_mem
-- name    : Formalism.FourierDecayAlt.P.DeterminantVectorSums.aeval_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:32:47.822799+00:00
-- url     : https://prove2.me/theorems/3d11ff73-fbf6-4ddf-864a-5a7370651285
-- title:
--   Determinant Vector Sums: aeval mem
-- statement:
--   The Determinant Vector Sums construction uses the aeval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L144-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L144-L150

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem Formalism.FourierDecayAlt.P.DeterminantVectorSums.aeval_mem (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G) (q : ℂ[X]) :
    ∀ x ∈ G, aeval K q x ∈ G := by sorry
