-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_proj_keeps_letter
-- name    : Formalism.MainNotions.PlaneGram.proj_keeps_letter
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:07:17.20333+00:00
-- url     : https://prove2.me/theorems/0b998d12-e581-4103-8019-1a9ad7700d03
-- title:
--   Plane Gram: proj keeps letter
-- statement:
--   The Plane Gram construction uses the proj keeps letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ProjKeepsLetter.lean#L138-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ProjKeepsLetter.lean#L138-L165

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.proj_keeps_letter (d : L → ℕ)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K) (i : L)
    (hcomm : ∀ (a : Fin r), ∀ F ∈ PolK K r d,
      Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) (a : Fin r) : ζ' (i, a) = ζ (i, a) := by sorry
