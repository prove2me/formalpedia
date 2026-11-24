-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_Jx_eq
-- name    : Formalism.FourierDecayAlt.P.Qx4.Dec.Jx_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:19:47.259423+00:00
-- url     : https://prove2.me/theorems/2fb0b838-bd60-4d80-b880-0604aaad8da6
-- title:
--   Dec: Jx eq
-- statement:
--   The Dec construction uses the Jx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L874-L878
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L874-L878

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.Qx4.Dec.Jx_eq {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') (z z' : Fin (2 * r + k + 1) → ℂ) (φ : ℂ → ℂ)
    (Ψ : Mx k r → (Wq →L[ℂ] Wp)) :
    Jx k r l z z' φ Ψ g = (psi k r z cStd u * psi k r z' cStd u') • (φ c • Ψ g₁) := by sorry
