-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_filter_PT
-- name    : Formalism.FourierDecayAlt.P.TA1.filter_PT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:08.405807+00:00
-- url     : https://prove2.me/theorems/200c1ca5-7362-4bf5-992c-79de84e50993
-- title:
--   TA1: filter PT
-- statement:
--   The TA1 construction uses the filter PT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L92-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L92-L106

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} [DecidableEq E]

theorem Formalism.FourierDecayAlt.P.TA1.filter_PT (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) :
    (PT Sg i).filter (fun p => ls p = s) =
      ((PT Sg (i - s)) ×ˢ (Sg i s)).image (fun x => Formalism.FourierDecayAlt.TA.ext x.1 s x.2) := by sorry
