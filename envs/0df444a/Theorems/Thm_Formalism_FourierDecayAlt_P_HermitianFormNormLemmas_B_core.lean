-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_core
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:25.004479+00:00
-- url     : https://prove2.me/theorems/3c85ec85-0c98-479b-a17a-17c351a7b14c
-- title:
--   B: core
-- statement:
--   The B construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L224-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L224-L249

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
variable {Cl Nu : Type}

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.core (hS4 : Formalism.HermitianLatticeCounting.S4.Step4) (L : LocalNG Cl Nu) (κ : ℕ) (Xp Yp : L.P → ℝ)
    (hX : ∀ p, 1 ≤ Xp p) (hY : ∀ p, 1 ≤ Yp p) (hb : L.Basic)
    (h1 : ∀ p ∈ L.Om, ∑ d, L.wt p d * ‖L.aN p d‖ ^ 2 ≤ Xp p * ((L.q p : ℝ) ^ κ)⁻¹ * L.nn p)
    (h2 : ∀ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 ≤ Xp p * L.nn p)
    (h3 : ∀ p, L.nn p ≤ Yp p * L.ngen p) :
    ∑ d, (∏ p, L.wt p (d p)) * ‖L.ampNG d‖ ^ 2 ≤
      (4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, L.ngen p := by sorry
