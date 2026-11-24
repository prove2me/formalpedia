-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_prod_rename
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_prod_rename
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:08.744255+00:00
-- url     : https://prove2.me/theorems/6d0acaae-18ff-4589-bf63-79e8996a1beb
-- title:
--   Gen: coeff prod rename
-- statement:
--   The Gen construction uses the coeff prod rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L122-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L122-L130

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}
variable [Fintype Pl]
variable [DecidableEq Pl]

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_prod_rename (P : ∀ v, MvPolynomial (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    MvPolynomial.coeff n (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) =
      ∏ v, MvPolynomial.coeff (eqv n v) (P v) := by sorry
