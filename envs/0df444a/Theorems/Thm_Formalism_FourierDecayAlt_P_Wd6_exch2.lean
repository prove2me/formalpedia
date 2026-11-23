-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_exch2
-- name    : Formalism.FourierDecayAlt.P.Wd6.exch2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:06.82624+00:00
-- url     : https://prove2.me/theorems/6e78de08-b43c-417b-a11d-e7fb26d397f8
-- title:
--   Wd6: exch2
-- statement:
--   The Wd6 construction uses the exch2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L451-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L451-L491

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

theorem Formalism.FourierDecayAlt.P.Wd6.exch2 (σ : Site A) (w : List (Letter K S)) (Y : K) (hσ : IsSite σ)
    (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : ∀ l ∈ w, star l.pt = l.pt) (hY : star Y = Y) :
    lift0 (Ts σ Y)ᴴ * Xm w Y * d0 (bT σ w) = d0 (bT σ w) * Xm w Y * lift0 (Ts σ Y)ᴴ := by sorry
