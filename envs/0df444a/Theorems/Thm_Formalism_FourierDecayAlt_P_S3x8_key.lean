-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_key
-- name    : Formalism.FourierDecayAlt.P.S3x8.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:27.788433+00:00
-- url     : https://prove2.me/theorems/e31d9bf6-194e-4698-acc7-be87ce5653a7
-- title:
--   S3x8: key
-- statement:
--   The S3x8 construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L41-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L41-L132

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A F : Type} [CommRing A] [CommRing F]

theorem Formalism.FourierDecayAlt.P.S3x8.key (φ : A →+* F) (hφ : Function.Injective φ) (I : AddSubgroup F)
    (hI : ∀ a x, x ∈ I → φ a * x ∈ I) :
    ∀ (r : ℕ) (M M' : Matrix (Fin r) (Fin r) A) (L U : Matrix (Fin r) (Fin r) F),
      IsLowUni L → IsUpUni U → L * M'.map φ = M.map φ * U →
      (∀ a b, φ (M' a b - M a b) ∈ I) →
      (∀ (l : ℕ) (hl : l ≤ r), IsUnit (lead M l hl)) →
      (∀ a b, (L - 1) a b ∈ I) ∧ (∀ a b, (U - 1) a b ∈ I) ∧
        ∀ (l : ℕ) (hl : l ≤ r), lead M' l hl = lead M l hl := by sorry
