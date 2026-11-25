-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_ChainPf_hasDerivAt_list_sum
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.hasDerivAt_list_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:20:52.982453+00:00
-- url     : https://prove2.me/theorems/e0425fed-40c1-47bd-a8f8-c5eddff0f16e
-- title:
--   Chain Pf: has Deriv At list sum
-- statement:
--   The Chain Pf construction uses the has Deriv At list sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L24-L31

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

theorem Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.hasDerivAt_list_sum {ι : Type} (l : List ι) (f : ι → ℝ → E') (f' : ι → E')
    (h : ∀ i ∈ l, HasDerivAt (f i) (f' i) 0) :
    HasDerivAt (fun s => (l.map fun i => f i s).sum) (l.map f').sum 0 := by sorry
