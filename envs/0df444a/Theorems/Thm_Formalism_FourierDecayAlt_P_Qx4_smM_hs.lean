-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_hs
-- name    : Formalism.FourierDecayAlt.P.Qx4.smM_hs
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:25:54.327076+00:00
-- url     : https://prove2.me/theorems/507a35eb-18a1-4de3-8478-ea7046e529c5
-- title:
--   Qx4: sm M hs
-- statement:
--   The Qx4 construction uses the sm M hs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L782-L787
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean#L782-L787

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
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx4.smM_hs (H : Matrix (Fin m) (Fin m) ℂ) {p v : X → Fin m → ℂ} {σ : X → ℂ} {s : Set X} (hp : SmV p s) (hv : SmV v s)
    (hσ : ContDiffOn ℝ ∞ σ s) : SmM (fun x => hs H (p x) (v x) (σ x)) s := by sorry
