-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_ptSize_loc
-- name    : Formalism.FourierDecayAlt.P.PBA.ptSize_loc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:54:25.177609+00:00
-- url     : https://prove2.me/theorems/98348405-0e75-4d13-ad9a-650a1e73f5d0
-- title:
--   PBA: pt Size loc
-- statement:
--   The PBA construction uses the pt Size loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L64-L66

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

theorem Formalism.FourierDecayAlt.P.PBA.ptSize_loc (σ : E →+* ℂ) (h : TB.Pt E) : D.ptSize (C.loc σ h) = TB.level h := by sorry
