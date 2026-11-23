-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_inverse_corner
-- name    : Formalism.FourierDecayAlt.P.S3x7.inverse_corner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:19.514737+00:00
-- url     : https://prove2.me/theorems/ea9391b0-a90e-4bd5-984a-82b263a4e0ec
-- title:
--   S3x7: inverse corner
-- statement:
--   The S3x7 construction uses the inverse corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L402-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L402-L451

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]

theorem Formalism.FourierDecayAlt.P.S3x7.inverse_corner {ϖ : o} (hϖ : Irreducible ϖ) {r k : ℕ} (j : Matrix (Idx r k) (Idx r k) o)
    (X : Matrix (Fin r) (Fin r) o) (hj : KppO j) (hX : b31 j = ϖ • X) :
    ∃ Y : Matrix (Fin r) (Fin r) o, b31 j⁻¹ = ϖ • Y ∧
      ((b33 j) * Y * (b11 j)).map (IsLocalRing.residue o) = -(X.map (IsLocalRing.residue o)) ∧
      ∀ (l : ℕ) (hl : l ≤ r),
        IsLocalRing.residue o (cm Y l hl) = (-1) ^ l * IsLocalRing.residue o (cm X l hl) := by sorry
