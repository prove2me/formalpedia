-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_appL
-- name    : Formalism.MainNotions.PlaneGram.cge_appL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:06:14.217836+00:00
-- url     : https://prove2.me/theorems/e401808a-e021-4eee-85b0-4d3b8147940e
-- title:
--   Plane Gram: cge app L
-- statement:
--   The Plane Gram construction uses the cge app L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L305-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L305-L312

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]

theorem Formalism.MainNotions.PlaneGram.cge_appL (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K)
    (ρ' δ κ : I → (Fin r →₀ ℕ)) (hcf : ∀ s, 0 ≤ v (cf s)) {a : ℝ} {G : MvPolynomial (L × Fin r) K}
    (hG : cge v a G) : cge v a (appL i P cls cf ρ' δ κ G) := by sorry
