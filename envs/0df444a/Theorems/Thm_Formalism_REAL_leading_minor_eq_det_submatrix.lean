-- Prove2me | Theorems.Thm_Formalism_REAL_leading_minor_eq_det_submatrix
-- name    : Formalism.REAL.leading_minor_eq_det_submatrix
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:14.493803+00:00
-- url     : https://prove2.me/theorems/c58911f0-8c05-4a91-acfb-9d4bc229af65
-- title:
--   REAL: leading minor eq det submatrix
-- statement:
--   The REAL construction uses the leading minor eq det submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/LeadingMinorEqDetSubmatrix.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/LeadingMinorEqDetSubmatrix.lean#L25-L27

import Definitions.Def_Formalism_RealPlaceAnalysis_LminorPos
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LeadingMinorEqDetSubmatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.leading_minor_eq_det_submatrix {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) :
    lminor x i = (x.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt))
      (Fin.castLE (Nat.lt_succ_iff.mp i.isLt))).det := by sorry
