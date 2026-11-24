-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_near_update
-- name    : Formalism.FourierDecayAlt.P.Qx6.near_update
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:35:27.900101+00:00
-- url     : https://prove2.me/theorems/da5514c9-5b3c-48fd-8c76-17c6cd77d1e0
-- title:
--   Qx6: near update
-- statement:
--   The Qx6 construction uses the near update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1337-L1350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1337-L1350

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable {L : Fin (r + 1)} {Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)}
variable {S : Set (Fin r → ℂ)}

theorem Formalism.FourierDecayAlt.P.Qx6.near_update {Dc : (Fin r → ℂ) → Set (Mx k r)} (ho : IsOpen (UU Dc)) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hgD : g ∈ Dc c) (l : Fin r) :
    ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ OmX r ∧ g ∈ Dc (Function.update c l s) := by sorry
