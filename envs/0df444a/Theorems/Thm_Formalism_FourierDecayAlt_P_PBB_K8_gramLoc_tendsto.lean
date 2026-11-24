-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_gramLoc_tendsto
-- name    : Formalism.FourierDecayAlt.P.PBB.K8.gramLoc_tendsto
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:15.378197+00:00
-- url     : https://prove2.me/theorems/fd485e8d-db1f-405d-b836-425266023dca
-- title:
--   K8: gram Loc tendsto
-- statement:
--   The K8 construction uses the gram Loc tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramLocTendsto.lean#L136-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramLocTendsto.lean#L136-L143

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramLocTendsto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBB Formalism.FourierDecayAlt.P.PBB.K8
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem Formalism.FourierDecayAlt.P.PBB.K8.gramLoc_tendsto (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) (i : ℕ) (w : S.W) (p q : C.LPt) :
    Tendsto (fun n => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) p q) atTop
      (𝓝 (S.gramLoc v ε i (w.1 v) p q)) := by sorry
