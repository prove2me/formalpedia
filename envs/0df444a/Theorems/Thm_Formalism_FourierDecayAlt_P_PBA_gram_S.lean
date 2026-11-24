-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_gram_S
-- name    : Formalism.FourierDecayAlt.P.PBA.gram_S
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:43.338895+00:00
-- url     : https://prove2.me/theorems/1f9a3b5b-2263-44fb-a082-616ebcb4b0ec
-- title:
--   PBA: gram S
-- statement:
--   The PBA construction uses the gram S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalNormNonneg.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalNormNonneg.lean#L82-L85

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

theorem Formalism.FourierDecayAlt.P.PBA.gram_S (ε : ℝ) (i : ℕ) (w : C.Word S.f) (p q : TB.Pt E) :
    S.gram ε i w p q = if i ≤ S.G.r + 1 then ∏ v, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G
      (C.loc (S.σ v) p)) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        (S.pd v).RR ε i (w v) (C.loc (S.σ v) p) (C.loc (S.σ v) q) else 0 := by sorry
