-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_local_norm_nonneg_alt
-- name    : Formalism.FourierDecayAlt.P.PBA.local_norm_nonneg_alt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:50.342653+00:00
-- url     : https://prove2.me/theorems/d203147a-2585-470e-8fcb-3c41c1030507
-- title:
--   PBA: local norm nonneg alt
-- statement:
--   The PBA construction uses the local norm nonneg alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalNormNonneg.lean#L149-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalNormNonneg.lean#L149-L157

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

theorem Formalism.FourierDecayAlt.P.PBA.local_norm_nonneg_alt {S : C.HidaSetting E Wp Wq} (hP : C.ThmPPos S) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W)
    (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (hκ : TB.PSDOn Y κ) : 0 ≤ S.base.N0 ε k w Y κ := by sorry
