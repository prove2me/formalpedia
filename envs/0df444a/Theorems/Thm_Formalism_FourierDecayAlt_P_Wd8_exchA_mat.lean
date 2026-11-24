-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exchA_mat
-- name    : Formalism.FourierDecayAlt.P.Wd8.exchA_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:16.546635+00:00
-- url     : https://prove2.me/theorems/d96cbadd-71af-4583-be51-e7b54a7d2275
-- title:
--   Wd8: exch A mat
-- statement:
--   The Wd8 construction uses the exch A mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L269-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L269-L278

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd8.exchA_mat (sites : List (Site A)) (w : List (Letter K S)) (Y : K)
    (h1 : ∀ σ ∈ sites, Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w) = d0 (bT σ w) * lift0 (Ts σ Y) * Xp w Y)
    (h2 : sites.Pairwise SitesCommute) :
    Xp w Y * lift0 (sites.map fun σ => Ts σ Y).prod * d0 (sites.map fun σ => bT σ w).prod =
      d0 (sites.map fun σ => bT σ w).prod * lift0 (sites.map fun σ => Ts σ Y).prod * Xp w Y := by sorry
