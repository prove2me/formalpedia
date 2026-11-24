-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_psi_lev
-- name    : Formalism.FourierDecayAlt.P.Qx4.psi_lev
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:43:17.035854+00:00
-- url     : https://prove2.me/theorems/78a9cf9f-745f-4505-b239-1c5cef59e750
-- title:
--   Qx4: psi lev
-- statement:
--   The Qx4 construction uses the psi lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L1069-L1071
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L1069-L1071

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
variable {r' : ℕ}
open Formalism.FourierDecayAlt.B2 (a0)
open B2x6 (lv blk)

theorem Formalism.FourierDecayAlt.P.Qx4.psi_lev (z : Fin (2 * r' + k + 1) → ℂ) (c : ℂ) (g : Mx k r') :
    psi k (1 + r') (liftVec k 1 r' z) c (ιLev k 1 r' g) = psi k r' z c g := by sorry
