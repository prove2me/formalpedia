-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hs_mem
-- name    : Formalism.FourierDecayAlt.P.Qx4.hs_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:22:02.874096+00:00
-- url     : https://prove2.me/theorems/88e6d72e-4fdb-429f-bc9e-554a1521f548
-- title:
--   Qx4: hs mem
-- statement:
--   The Qx4 construction uses the hs mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L48-L57

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
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

theorem Formalism.FourierDecayAlt.P.Qx4.hs_mem (hH : Hᴴ = H) {p v : Fin n → ℂ} {σ : ℂ} (hpp : herm H p p = 0) (hvp : herm H v p = 0)
    (hσ : σ + conj σ + herm H v v = 0) : hs H p v σ ∈ UH H := by sorry
