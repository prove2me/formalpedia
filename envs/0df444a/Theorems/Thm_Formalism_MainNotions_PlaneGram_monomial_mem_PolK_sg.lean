-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_monomial_mem_PolK_sg
-- name    : Formalism.MainNotions.PlaneGram.monomial_mem_PolK_sg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:37.384526+00:00
-- url     : https://prove2.me/theorems/0206c7cf-35c4-4118-9e54-913e085ac926
-- title:
--   Plane Gram: monomial mem Pol K sg
-- statement:
--   The Plane Gram construction uses the monomial mem Pol K sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L9-L14

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
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

theorem Formalism.MainNotions.PlaneGram.monomial_mem_PolK_sg {K : Type} [Field K] {L : Type} {r : ℕ} (d : L → ℕ) (α : L × Fin r →₀ ℕ)
    (c : K) (h : ∀ i, ldeg α i = d i) : monomial α c ∈ PolK K r d := by sorry
