-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_cs
-- name    : Formalism.FourierDecayAlt.P.c2x3_cs
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:36:51.773975+00:00
-- url     : https://prove2.me/theorems/f1bf8712-2610-47c1-9231-ac2b7d6bc56d
-- title:
--   P: c2x3 cs
-- statement:
--   The P construction uses the c2x3 cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L123-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L123-L165

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
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
open C2x2

theorem Formalism.FourierDecayAlt.P.c2x3_cs {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (U : Submodule ℂ (Fin n → ℂ))
    (hpos : ∀ v ∈ U, v ≠ 0 → 0 < (herm H v v).re) (a b : Fin n → ℂ) (ha : a ∈ U) (hb : b ∈ U) :
    Complex.normSq (herm H a b) ≤ (herm H a a).re * (herm H b b).re := by sorry
