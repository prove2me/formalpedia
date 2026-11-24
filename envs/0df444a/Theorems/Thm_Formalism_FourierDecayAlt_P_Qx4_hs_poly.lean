-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hs_poly
-- name    : Formalism.FourierDecayAlt.P.Qx4.hs_poly
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:21:05.18437+00:00
-- url     : https://prove2.me/theorems/bdf663ff-94a3-4024-be4f-5de25b4c2f5b
-- title:
--   Qx4: hs poly
-- statement:
--   The Qx4 construction uses the hs poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L461-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L461-L468

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)

theorem Formalism.FourierDecayAlt.P.Qx4.hs_poly (p v₀ : Fin (2 * r + k + 1) → ℂ) (κ : ℂ) (t : ℝ) :
    hs (Hpk k r) p ((t : ℂ) • v₀) ((t : ℂ) ^ 2 * κ) =
      1 + (t : ℂ) • (Matrix.vecMulVec v₀ (fun j => ⟪bvec j, p⟫) - Matrix.vecMulVec p (fun j => ⟪bvec j, v₀⟫)) +
        ((t : ℂ) ^ 2 * κ) • Matrix.vecMulVec p (fun j => ⟪bvec j, p⟫) := by sorry
