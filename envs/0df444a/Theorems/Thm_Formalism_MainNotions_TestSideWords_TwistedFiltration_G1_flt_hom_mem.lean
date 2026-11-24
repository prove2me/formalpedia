-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_hom_mem
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_hom_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:33.33124+00:00
-- url     : https://prove2.me/theorems/1f079ec4-48bc-4b6c-a129-feb895b49d2f
-- title:
--   G1: flt hom mem
-- statement:
--   The G1 construction uses the flt hom mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L169-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean#L169-L181

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_hom_mem {B₀ B' : Type*} [CommRing B₀] [CommRing B'] {σ : Type*} (Fl : flt_Fil B₀) (Fl' : flt_Fil B')
    (φ : MvPolynomial σ B₀ →+* B') (wt : (σ →₀ ℕ) →+ ℤ)
    (hC : ∀ (t : ℤ) (b : B₀), b ∈ Fl.F t → φ (C b) ∈ Fl'.F t)
    (hX : ∀ w, φ (X w) ∈ Fl'.F (wt (Finsupp.single w 1))) {t : ℤ} {P : MvPolynomial σ B₀}
    (hP : P ∈ (flt_lift Fl wt).F t) : φ P ∈ Fl'.F t := by sorry
