-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_sum
-- name    : Formalism.FourierDecayAlt.P.NFx2.isPF_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:11:04.802796+00:00
-- url     : https://prove2.me/theorems/595d3209-d34f-468b-beba-e6d5526e3721
-- title:
--   NFx2: is PF sum
-- statement:
--   The NFx2 construction uses the is PF sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L94-L96

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_UpperTheory_Reformulated_B_IsPFSum_isPF_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem Formalism.FourierDecayAlt.P.NFx2.isPF_sum {ι : Type} (s : Finset ι) {f : ι → ℂ → A} (hf : ∀ i ∈ s, IsPF (f i)) :
    IsPF fun Y => ∑ i ∈ s, f i Y := by sorry
