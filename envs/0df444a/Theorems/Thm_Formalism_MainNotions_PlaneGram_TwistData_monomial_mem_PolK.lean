-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_monomial_mem_PolK
-- name    : Formalism.MainNotions.PlaneGram.TwistData.monomial_mem_PolK
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:05:14.482304+00:00
-- url     : https://prove2.me/theorems/deb795b8-fc73-4cd5-b0fe-9022a1e58820
-- title:
--   Twist Data: monomial mem Pol K
-- statement:
--   The Twist Data construction uses the monomial mem Pol K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L35-L42

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)

theorem Formalism.MainNotions.PlaneGram.TwistData.monomial_mem_PolK {L : Type} {r : ℕ} (d : L → ℕ) (α : L × Fin r →₀ ℕ) (c : K)
    (h : ∀ i, ldeg α i = d i) : monomial α c ∈ PolK K r d := by sorry
