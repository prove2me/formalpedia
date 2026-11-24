-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_smul_r
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.herm_smul_r
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:44:55.599979+00:00
-- url     : https://prove2.me/theorems/2766d244-ef85-41ef-9ded-a8efce6a08c5
-- title:
--   Hermitian Xi Vector: herm smul r
-- statement:
--   The Hermitian Xi Vector construction uses the herm smul r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L26-L29

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

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.herm_smul_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (v a : Fin n → ℂ) :
    herm H v (s • a) = conj s * herm H v a := by sorry
