-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_lcomp_comm
-- name    : Formalism.CountingSumsFrames.lcomp_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:17.56681+00:00
-- url     : https://prove2.me/theorems/c699a67a-6077-4b7c-a303-c81b3287b17f
-- title:
--   Counting Sums Frames: lcomp comm
-- statement:
--   The Counting Sums Frames construction uses the lcomp comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L75-L83

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]

theorem Formalism.CountingSumsFrames.lcomp_comm (φ : ι → V →ₗ[K] V) (π : V →ₗ[K] V) (C : Set V) :
    ∀ l : List ι, (∀ j ∈ l, ∀ u ∈ C, φ j u ∈ C) → (∀ j ∈ l, ∀ u ∈ C, π (φ j u) = φ j (π u)) →
      ∀ u ∈ C, π (lcomp φ l u) = lcomp φ l (π u)
  := by sorry
