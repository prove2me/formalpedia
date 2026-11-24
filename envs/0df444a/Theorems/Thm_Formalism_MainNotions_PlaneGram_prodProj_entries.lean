-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_prodProj_entries
-- name    : Formalism.MainNotions.PlaneGram.prodProj_entries
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:08:10.35618+00:00
-- url     : https://prove2.me/theorems/f513a9f8-a0d2-49d1-aa52-ba4e7807a356
-- title:
--   Plane Gram: prod Proj entries
-- statement:
--   The Plane Gram construction uses the prod Proj entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ProjKeepsLetter.lean#L169-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ProjKeepsLetter.lean#L169-L190

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

theorem Formalism.MainNotions.PlaneGram.prodProj_entries {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r]
    (d : L → ℕ) {ι : Type} (s : Finset ι) (S : ι → Finset L)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (h1 : ∀ F ∈ PolK K r d, Pr F ∈ PolK K r d)
    (h6 : ∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) :
    (∀ k, ldeg ζ' k = d k) ∧
      ∀ i, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ a, ζ' (i, a) = ζ (i, a) := by sorry
