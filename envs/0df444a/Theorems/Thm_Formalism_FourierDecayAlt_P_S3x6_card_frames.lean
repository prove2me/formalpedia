-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_card_frames
-- name    : Formalism.FourierDecayAlt.P.S3x6.card_frames
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:32.171799+00:00
-- url     : https://prove2.me/theorems/2b1b424f-3ee3-4252-a1b5-bb55d4b354cc
-- title:
--   S3x6: card frames
-- statement:
--   The S3x6 construction uses the card frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L179-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L179-L203

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}

theorem Formalism.FourierDecayAlt.P.S3x6.card_frames (hσ : Inv σ) [Finite K] (s : ℕ → ℕ)
    (hs : ∀ n, Nat.card {w : Fin n → K // ∑ i, σ (w i) * w i = 1} = s n) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K),
    Herm h → Nondeg h → finrank K V = n →
    Nat.card {b : Fin n → V // Ortho h b} = ∏ j ∈ Finset.range n, s (j + 1) := by sorry
