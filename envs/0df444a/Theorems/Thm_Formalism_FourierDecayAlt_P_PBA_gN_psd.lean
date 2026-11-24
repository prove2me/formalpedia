-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_gN_psd
-- name    : Formalism.FourierDecayAlt.P.PBA.gN_psd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:07:14.817525+00:00
-- url     : https://prove2.me/theorems/3de3c4ca-0f8b-4cb8-aaaa-b65e17838baf
-- title:
--   PBA: g N psd
-- statement:
--   The PBA construction uses the g N psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L75-L85

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)

theorem Formalism.FourierDecayAlt.P.PBA.gN_psd (hpos : C.ThmPPos S) (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) {i : ℕ} (hi : i ≤ S.G.r + 1) (w0 : S.W)
    (Y : Finset C.LPt) : TB.PSDOn Y (KB.gN S v ε i (w0.1 v)) := by sorry
