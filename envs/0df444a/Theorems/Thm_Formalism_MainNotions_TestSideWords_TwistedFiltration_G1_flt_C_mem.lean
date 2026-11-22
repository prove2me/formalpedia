-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_C_mem
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_C_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:11.006808+00:00
-- url     : https://prove2.me/theorems/f604a24e-6fbc-4758-b939-dd9da99f69ed
-- title:
--   G1: flt C mem
-- statement:
--   The G1 construction uses the flt C mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L137-L140

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_C_mem {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {a : B} (ha : a ∈ Fl.F t) : (C a : MvPolynomial σ B) ∈ (flt_lift Fl wt).F t := by sorry
