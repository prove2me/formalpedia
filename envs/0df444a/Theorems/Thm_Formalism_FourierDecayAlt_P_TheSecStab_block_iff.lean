-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_block_iff
-- name    : Formalism.FourierDecayAlt.P.TheSecStab.block_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:22:11.293954+00:00
-- url     : https://prove2.me/theorems/6ba9fa82-8e4d-43c4-8fdc-74f680c822c3
-- title:
--   The Sec Stab: block iff
-- statement:
--   The The Sec Stab construction uses the block iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L211-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L211-L294

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
variable {k : ℕ}

theorem Formalism.FourierDecayAlt.P.TheSecStab.block_iff (hk : 1 ≤ k) {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ)
    {μ μ' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) (hμ' : μ' ∈ UH (Hb k))
    (hμa : μ *ᵥ a = a) (hμb : μ' *ᵥ b = b) :
    μ * theSecB k a b T T' ζ * μ' = theSecB k a b T T' ζ ↔
      ((gA k a T)⁻¹ * μ * gA k a T) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
        gB k b T' * μ' * (gB k b T')⁻¹ = ((gA k a T)⁻¹ * μ * gA k a T)⁻¹ := by sorry
