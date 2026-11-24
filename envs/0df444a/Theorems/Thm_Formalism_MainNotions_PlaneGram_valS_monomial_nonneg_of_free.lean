-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_monomial_nonneg_of_free
-- name    : Formalism.MainNotions.PlaneGram.valS_monomial_nonneg_of_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:10.428051+00:00
-- url     : https://prove2.me/theorems/b9a6dac0-6fce-41bf-ad2e-ffaa477e4393
-- title:
--   Plane Gram: val S monomial nonneg of free
-- statement:
--   The Plane Gram construction uses the val S monomial nonneg of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1175-L1182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1175-L1182

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
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
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {L : Type} [DecidableEq L] {r : ℕ} {sg : L → Bool} {S : Finset L}

theorem Formalism.MainNotions.PlaneGram.valS_monomial_nonneg_of_free (μ : L × Fin r →₀ ℕ) (c : K) (h : ∀ i ∈ S, ∀ a, μ (i, a) = 0) :
    0 ≤ valS sg S (monomial μ c) := by sorry
