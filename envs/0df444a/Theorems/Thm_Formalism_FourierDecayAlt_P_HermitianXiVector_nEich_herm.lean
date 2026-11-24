-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_nEich_herm
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_herm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:44:49.58618+00:00
-- url     : https://prove2.me/theorems/47e6c9ce-b7b0-4ba5-a4dc-22ab0f8aab0b
-- title:
--   Hermitian Xi Vector: n Eich herm
-- statement:
--   The Hermitian Xi Vector construction uses the n Eich herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L132-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L132-L152

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_herm {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) (y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (C2.nEich k r z ξ *ᵥ y) (C2.nEich k r z ξ *ᵥ y') = herm (Hpk k r) y y' := by sorry
