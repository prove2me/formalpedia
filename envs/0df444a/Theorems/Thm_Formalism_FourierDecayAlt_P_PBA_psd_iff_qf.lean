-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_psd_iff_qf
-- name    : Formalism.FourierDecayAlt.P.PBA.psd_iff_qf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:14:16.479268+00:00
-- url     : https://prove2.me/theorems/4e2cdf17-0524-45bd-bff1-7970684c787f
-- title:
--   PBA: psd iff qf
-- statement:
--   The PBA construction uses the psd iff qf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L46-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean#L46-L90

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
variable {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β)

theorem Formalism.FourierDecayAlt.P.PBA.psd_iff_qf {γ : Type} (Y : Finset γ) (k : γ → γ → ℂ) :
    TB.PSDOn Y k ↔ (∀ x ∈ Y, ∀ y ∈ Y, k y x = conj (k x y)) ∧ ∀ c, 0 ≤ (qf Y k c).re := by sorry
