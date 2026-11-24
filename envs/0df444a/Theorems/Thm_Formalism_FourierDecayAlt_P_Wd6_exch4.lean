-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_exch4
-- name    : Formalism.FourierDecayAlt.P.Wd6.exch4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:29.83162+00:00
-- url     : https://prove2.me/theorems/9f01b871-70a8-4edd-abf3-cd931aa4a7ee
-- title:
--   Wd6: exch4
-- statement:
--   The Wd6 construction uses the exch4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L501-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L501-L506

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd6.exch4 (σ : Site A) (w : List (Letter K S)) (Y : K) (hσ : IsSite σ)
    (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    lift0 (Ts σ Y)ᵀ * (Xp w Y)ᵀ * d0 (bT σ w) = d0 (bT σ w) * (Xp w Y)ᵀ * lift0 (Ts σ Y)ᵀ := by sorry
