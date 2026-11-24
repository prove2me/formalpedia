-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_theSecB_core
-- name    : Formalism.FourierDecayAlt.P.TheSec.theSecB_core
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:48:02.447326+00:00
-- url     : https://prove2.me/theorems/78fa9421-34fc-4ec2-96f9-0888630db4ad
-- title:
--   The Sec: the Sec B core
-- statement:
--   The The Sec construction uses the the Sec B core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSection.lean#L191-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSection.lean#L191-L292

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction
variable (k : ℕ)

theorem Formalism.FourierDecayAlt.P.TheSec.theSecB_core (hk : 1 ≤ k) (a b : Fin (k + 1) → ℂ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) :
    (∀ i j, ContDiffOn ℝ ∞ (fun ζ => theSecB k a b T T' ζ i j) {ζ : ℂ | T * T' < Complex.normSq ζ}) ∧
      ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
        (theSecB k a b T T' ζ)ᴴ * Hb k * theSecB k a b T T' ζ = Hb k ∧
          herm (Hb k) (theSecB k a b T T' ζ *ᵥ b) a = ζ := by sorry
