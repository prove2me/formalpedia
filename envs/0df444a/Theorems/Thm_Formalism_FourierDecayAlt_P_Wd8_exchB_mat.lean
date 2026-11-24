-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exchB_mat
-- name    : Formalism.FourierDecayAlt.P.Wd8.exchB_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:30.160803+00:00
-- url     : https://prove2.me/theorems/71c0e233-19e3-4519-8e24-d9fff17d3adf
-- title:
--   Wd8: exch B mat
-- statement:
--   The Wd8 construction uses the exch B mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L290-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L290-L300

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

theorem Formalism.FourierDecayAlt.P.Wd8.exchB_mat (sites : List (Site A)) (w : List (Letter K S)) (Y : K)
    (h1 : ∀ σ ∈ sites,
      lift0 (Ts σ Y)ᴴ * Xm w Y * d0 (bT σ w) = d0 (bT σ w) * Xm w Y * lift0 (Ts σ Y)ᴴ)
    (h2 : sites.Pairwise SitesCommute) :
    lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * Xm w Y * d0 (sites.map fun σ => bT σ w).prod =
      d0 (sites.map fun σ => bT σ w).prod * Xm w Y * lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ := by sorry
