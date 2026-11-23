-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ldu
-- name    : Formalism.FourierDecayAlt.P.S3x7.border_ldu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:40.032121+00:00
-- url     : https://prove2.me/theorems/6dfb4e19-8cc0-4498-a3f4-16d7ca10d11a
-- title:
--   S3x7: border ldu
-- statement:
--   The S3x7 construction uses the border ldu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L252-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L252-L265

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
variable {A : Type} [CommRing A]

theorem Formalism.FourierDecayAlt.P.S3x7.border_ldu {r : ℕ} (B L₀ D₀ U₀ : Matrix (Fin r) (Fin r) A) (v u : Fin r → A) (c : A)
    (uB : IsUnit B.det) (e₀ : B = L₀ * D₀ * U₀) :
    border B v u c = border L₀ 0 (u ᵥ* (B⁻¹ * L₀)) 1 *
      border D₀ 0 0 (c - ((u ᵥ* (B⁻¹ * L₀)) ᵥ* D₀) ⬝ᵥ ((U₀ * B⁻¹) *ᵥ v)) *
      border U₀ ((U₀ * B⁻¹) *ᵥ v) 0 1 := by sorry
