-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WittOrthonormalBasis_witt_nd
-- name    : Formalism.FourierDecayAlt.P.WittOrthonormalBasis.witt_nd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:02:54.432639+00:00
-- url     : https://prove2.me/theorems/9ade18e0-cbf2-49c3-bdd4-bcb0488bf55d
-- title:
--   Witt Orthonormal Basis: witt nd
-- statement:
--   The Witt Orthonormal Basis construction uses the witt nd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WittOrthonormalBasis.lean#L117-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WittOrthonormalBasis.lean#L117-L172

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WittOrthonormalBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.WittOrthonormalBasis
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector FlagGramRestriction
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.WittOrthonormalBasis.witt_nd {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {g₁ g₂ : B.Mat k r}
    (hp1 : C2.PosPt k r z z' g₁) (hp2 : C2.PosPt k r z z' g₂)
    (hΓ : (gnB k r z z' g₁)ᴴ * Hpk k r * gnB k r z z' g₁ = (gnB k r z z' g₂)ᴴ * Hpk k r * gnB k r z z' g₂) :
    ∃ s0 ∈ B.GV k r, s0 * gnB k r z z' g₁ = gnB k r z z' g₂ := by sorry
