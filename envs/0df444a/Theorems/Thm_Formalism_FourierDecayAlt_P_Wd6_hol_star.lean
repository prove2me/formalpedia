-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_hol_star
-- name    : Formalism.FourierDecayAlt.P.Wd6.hol_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:04.834187+00:00
-- url     : https://prove2.me/theorems/6df90443-2edc-4c34-9a90-20235880bfa6
-- title:
--   Wd6: hol star
-- statement:
--   The Wd6 construction uses the hol star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L344-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L344-L361

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

theorem Formalism.FourierDecayAlt.P.Wd6.hol_star {σ : Site A} (hσ : IsSite σ) (Y Y' : K) (i j r s : Fin 2) :
    Commute (Ts σ Y i j) (star (Ts σ Y' r s)) := by sorry
