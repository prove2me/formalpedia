-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_herm_inv
-- name    : Formalism.FourierDecayAlt.P.Qx4.uh_herm_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:24:58.804382+00:00
-- url     : https://prove2.me/theorems/2c0725d7-06e5-46a0-b516-0e94112876f2
-- title:
--   Qx4: uh herm inv
-- statement:
--   The Qx4 construction uses the uh herm inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L128-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L128-L129

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

theorem Formalism.FourierDecayAlt.P.Qx4.uh_herm_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) : ⟪g *ᵥ u, v⟫ = ⟪u, g⁻¹ *ᵥ v⟫ := by sorry
