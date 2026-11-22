-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_keyCm
-- name    : Formalism.FourierDecayAlt.P.S3x8.keyCm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:56.680614+00:00
-- url     : https://prove2.me/theorems/12f5a6ad-bd53-449a-b653-a543dd19a8ec
-- title:
--   S3x8: key Cm
-- statement:
--   The S3x8 construction uses the key Cm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L140-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L140-L161

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

theorem Formalism.FourierDecayAlt.P.S3x8.keyCm (φ : A →+* F) (hφ : Function.Injective φ) (I : AddSubgroup F)
    (hI : ∀ a x, x ∈ I → φ a * x ∈ I) {r : ℕ} (X X' : Matrix (Fin r) (Fin r) A)
    (v₂ v₁ : Matrix (Fin r) (Fin r) F) (h₂ : IsUpUni v₂) (h₁ : IsUpUni v₁)
    (hE : v₂ * X'.map φ = X.map φ * v₁) (hd : ∀ a b, φ (X' a b - X a b) ∈ I)
    (hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) :
    (∀ a b, (v₂ - 1) a b ∈ I) ∧ (∀ a b, (v₁ - 1) a b ∈ I) ∧
      ∀ (l : ℕ) (hl : l ≤ r), cm X' l hl = cm X l hl := by sorry
