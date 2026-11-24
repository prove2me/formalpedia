-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_sizeAt_nonneg
-- name    : Formalism.FourierDecayAlt.P.PBA.sizeAt_nonneg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:33.435863+00:00
-- url     : https://prove2.me/theorems/5a62cbf1-e40a-4d63-8440-6a1fcedcb219
-- title:
--   PBA: size At nonneg
-- statement:
--   The PBA construction uses the size At nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L68-L73

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

theorem Formalism.FourierDecayAlt.P.PBA.sizeAt_nonneg (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by sorry
