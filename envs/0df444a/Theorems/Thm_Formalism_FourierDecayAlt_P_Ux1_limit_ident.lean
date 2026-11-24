-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_limit_ident
-- name    : Formalism.FourierDecayAlt.P.Ux1.limit_ident
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:10:18.734965+00:00
-- url     : https://prove2.me/theorems/43da2888-5928-4240-8324-fbc4c33e382f
-- title:
--   Ux1: limit ident
-- statement:
--   The Ux1 construction uses the limit ident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L609-L650
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L609-L650

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.Ux1.limit_ident {a : ℝ} {mm : ℕ} (Fs : ℕ → Mat k r → E)
    (hC : ∀ n, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (Fs n))
    (K : List (Mat k r) → List (Mat k r) → Mat k r → E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ n (u w : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, ‖dLR u w (Fs n) g - K u w g‖ ≤ gN g ^ (-a) * ε n) :
    ∀ u w : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, dLR u w (K [] []) g = K u w g := by sorry
