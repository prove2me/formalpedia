-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_of
-- name    : Formalism.FourierDecayAlt.P.Qx6.good_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:33:25.143791+00:00
-- url     : https://prove2.me/theorems/4b50bd1b-eb01-48a3-9cd6-3f6572848ce5
-- title:
--   Qx6: good of
-- statement:
--   The Qx6 construction uses the good of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1737-L1747
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1737-L1747

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
variable {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.Qx6.good_of (hS : SData z z' L Dc Dc (OmX r)) {T : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp)}
    (hP : Pres2 (RS z z' π π' L Dc Dc (OmX r)) T T)
    (hl : ∀ Φ Ψ, FamFF k r z z' π π' L Dc Φ → FamFF k r z z' π π' L Dc Ψ → ∀ s : ℂ, ∀ c ∈ OmX r,
      ∀ g ∈ Glev k r L, g ∈ Dc c → T (Φ + s • Ψ) c g = T Φ c g + s • T Ψ c g) :
    (famData π π' hS).Good T := by sorry
