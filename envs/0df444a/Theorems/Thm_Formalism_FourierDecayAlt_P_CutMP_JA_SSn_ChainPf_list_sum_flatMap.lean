-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_ChainPf_list_sum_flatMap
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.list_sum_flatMap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:20:28.423276+00:00
-- url     : https://prove2.me/theorems/91d5f0a1-6cd5-459a-afad-6777f498600a
-- title:
--   Chain Pf: list sum flat Map
-- statement:
--   The Chain Pf construction uses the list sum flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L33-L37

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

theorem Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.list_sum_flatMap {ι κ : Type} (l : List ι) (f : ι → List κ) (g : κ → E') :
    ((l.flatMap f).map g).sum = (l.map fun i => ((f i).map g).sum).sum := by sorry
