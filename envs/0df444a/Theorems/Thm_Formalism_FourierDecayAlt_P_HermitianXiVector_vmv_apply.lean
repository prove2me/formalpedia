-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_vmv_apply
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.vmv_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:44:09.711352+00:00
-- url     : https://prove2.me/theorems/f2053c76-ee22-4245-aeda-c153a5c44650
-- title:
--   Hermitian Xi Vector: vmv apply
-- statement:
--   The Hermitian Xi Vector construction uses the vmv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L79-L88

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

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.vmv_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (a b y : Fin n → ℂ) :
    vecMulVec a (star (H *ᵥ b)) *ᵥ y = herm H y b • a := by sorry
