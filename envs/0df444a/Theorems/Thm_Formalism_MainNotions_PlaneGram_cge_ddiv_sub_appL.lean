-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_ddiv_sub_appL
-- name    : Formalism.MainNotions.PlaneGram.cge_ddiv_sub_appL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:05:49.117705+00:00
-- url     : https://prove2.me/theorems/f1c55977-2684-4247-8065-3c82ffbca0cb
-- title:
--   Plane Gram: cge ddiv sub app L
-- statement:
--   The Plane Gram construction uses the cge ddiv sub app L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L314-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L314-L327

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {K : Type} [Field K]
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]

theorem Formalism.MainNotions.PlaneGram.cge_ddiv_sub_appL (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (M : Fin r →₀ ℕ)
    (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)) (c : ℝ)
    (hder : ∀ η : Fin r →₀ ℕ, cge v c (ddiv M (monomial η (1 : K)) -
        ∑ s, if cls s = (fun a => η a % P) then
          monomial (ρ' s + P • (δ s + (divE P η - κ s))) (cf s * bin (κ s) (divE P η)) else 0))
    {a : ℝ} {G : MvPolynomial (L × Fin r) K} (hG : cge v a G) :
    cge v (a + c) (ddiv (onLetter i M) G - appL i P cls cf ρ' δ κ G) := by sorry
