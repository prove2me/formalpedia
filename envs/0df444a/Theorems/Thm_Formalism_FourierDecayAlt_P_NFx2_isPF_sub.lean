-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_sub
-- name    : Formalism.FourierDecayAlt.P.NFx2.isPF_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:12:55.900809+00:00
-- url     : https://prove2.me/theorems/da4b2f6c-5631-45bb-921d-a7c59b54b788
-- title:
--   NFx2: is PF sub
-- statement:
--   The NFx2 construction uses the is PF sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L84-L85

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
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

theorem Formalism.FourierDecayAlt.P.NFx2.isPF_sub {f g : ℂ → A} (hf : IsPF f) (hg : IsPF g) : IsPF fun Y => f Y - g Y := by sorry
