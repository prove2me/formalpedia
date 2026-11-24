-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_succ_iff
-- name    : Formalism.FourierDecayAlt.P.Qx4.glev_succ_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:44.887828+00:00
-- url     : https://prove2.me/theorems/66fc60e2-b488-47eb-a1e1-f66be8e1277a
-- title:
--   Qx4: glev succ iff
-- statement:
--   The Qx4 construction uses the glev succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L139-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L139-L153

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

theorem Formalism.FourierDecayAlt.P.Qx4.glev_succ_iff (l : Fin r) (g : Mx k r) : g ∈ Glev k r l.succ ↔
    g ∈ Glev k r l.castSucc ∧ g *ᵥ bvec (eI k r l) = bvec (eI k r l) ∧ g *ᵥ bvec (esI k r l) = bvec (esI k r l) := by sorry
