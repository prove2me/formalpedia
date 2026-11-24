-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hs_glev
-- name    : Formalism.FourierDecayAlt.P.Qx4.hs_glev
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:42:32.33213+00:00
-- url     : https://prove2.me/theorems/f470fe3c-359b-418a-8fbd-d54cdec97f14
-- title:
--   Qx4: hs glev
-- statement:
--   The Qx4 construction uses the hs glev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L230-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L230-L237

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

theorem Formalism.FourierDecayAlt.P.Qx4.hs_glev {i : Fin (r + 1)} {p v : Fin (2 * r + k + 1) → ℂ} {σ : ℂ} (hpp : ⟪p, p⟫ = 0) (hvp : ⟪v, p⟫ = 0)
    (hσ : σ + conj σ + ⟪v, v⟫ = 0)
    (hp : ∀ a : Fin r, a.val < i.val → ⟪bvec (eI k r a), p⟫ = 0 ∧ ⟪bvec (esI k r a), p⟫ = 0)
    (hv : ∀ a : Fin r, a.val < i.val → ⟪bvec (eI k r a), v⟫ = 0 ∧ ⟪bvec (esI k r a), v⟫ = 0) :
    hs (Hpk k r) p v σ ∈ Glev k r i := by sorry
