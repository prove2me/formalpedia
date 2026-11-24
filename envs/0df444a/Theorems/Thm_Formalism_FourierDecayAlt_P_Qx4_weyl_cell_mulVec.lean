-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_weyl_cell_mulVec
-- name    : Formalism.FourierDecayAlt.P.Qx4.weyl_cell_mulVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:45.75484+00:00
-- url     : https://prove2.me/theorems/25c93723-2217-4f6a-ad5d-a89146d47e5b
-- title:
--   Qx4: weyl cell mul Vec
-- statement:
--   The Qx4 construction uses the weyl cell mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L344-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L344-L359

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

theorem Formalism.FourierDecayAlt.P.Qx4.weyl_cell_mulVec (c : ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    w1 k r l c *ᵥ y = y + (c * ⟪y, 𝐬⟫ - ⟪y, 𝐞⟫) • 𝐬 + ((conj c)⁻¹ * ⟪y, 𝐞⟫ - ⟪y, 𝐬⟫) • 𝐞 := by sorry
