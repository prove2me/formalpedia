-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_ChainPf_chain_bound_holds
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.chain_bound_holds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:29:06.607737+00:00
-- url     : https://prove2.me/theorems/13fce1d3-b7e0-5cd4-a77e-e515c4e739d5
-- title:
--   Chain Pf: chain bound holds
-- statement:
--   The Chain Pf construction uses the chain bound holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L147-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L147-L269

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChainPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.chain_bound_holds : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainBd := by sorry
