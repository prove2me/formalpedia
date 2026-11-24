-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_gram_psd
-- name    : Formalism.FourierDecayAlt.P.PBA.gram_psd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:04:59.924882+00:00
-- url     : https://prove2.me/theorems/a0950e3b-18da-4f63-931f-40f2ae6c6153
-- title:
--   PBA: gram psd
-- statement:
--   The PBA construction uses the gram psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalNormNonneg.lean#L133-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalNormNonneg.lean#L133-L147

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
variable {S RR}

theorem Formalism.FourierDecayAlt.P.PBA.gram_psd {S : C.HidaSetting E Wp Wq} (hP : C.ThmPPos S) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W)
    (Y : Finset (TB.Pt E)) : TB.PSDOn Y (fun h h' => S.gram ε k w.1 h h') := by sorry
