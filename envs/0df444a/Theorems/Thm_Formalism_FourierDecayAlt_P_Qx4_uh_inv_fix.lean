-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv_fix
-- name    : Formalism.FourierDecayAlt.P.Qx4.uh_inv_fix
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:42:36.298806+00:00
-- url     : https://prove2.me/theorems/a7fb5745-94c7-40b4-9a98-d8b9ce96d760
-- title:
--   Qx4: uh inv fix
-- statement:
--   The Qx4 construction uses the uh inv fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L126-L127

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

theorem Formalism.FourierDecayAlt.P.Qx4.uh_inv_fix {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {v w : Fin (2 * r + k + 1) → ℂ} (h : g *ᵥ v = w) : g⁻¹ *ᵥ w = v := by sorry
