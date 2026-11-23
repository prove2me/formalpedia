-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_peel
-- name    : Formalism.CountingSumsFrames.peel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:48.869684+00:00
-- url     : https://prove2.me/theorems/a3fd3885-56af-4905-940e-64240a3e36d4
-- title:
--   Counting Sums Frames: peel
-- statement:
--   The Counting Sums Frames construction uses the peel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L85-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L85-L105

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

theorem Formalism.CountingSumsFrames.peel (B : V → V → K) (φ Ts π : ι → V →ₗ[K] V) (c : ι → K) (C : ι → Set V) (Y : Set V)
    (hYC : ∀ i, Y ⊆ C i) (hTY : ∀ i, ∀ y ∈ Y, Ts i y ∈ Y)
    (hkeep : ∀ i j, i < j → ∀ u ∈ C i, φ j u ∈ C i)
    (hcomm : ∀ i j, i < j → ∀ u ∈ C i, π i (φ j u) = φ j (π i u))
    (hadj : ∀ i, ∀ u ∈ C i, ∀ u' ∈ Y, B (φ i u) (Ts i u') = c i * B (π i u) u') :
    ∀ l : List ι, l.Pairwise (· < ·) → ∀ u ∈ Y, (∀ i ∈ l, π i u = u) → ∀ y ∈ Y,
      B (lcomp φ l u) (lcomp Ts l y) = (l.map c).prod * B u y
  := by sorry
