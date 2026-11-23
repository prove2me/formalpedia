-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_kpp_hn
-- name    : Formalism.FourierDecayAlt.P.S3x3.kpp_hn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:05.839442+00:00
-- url     : https://prove2.me/theorems/4e30ada2-1e37-4db5-9ac7-fbbfe8f91da4
-- title:
--   S3x3: kpp hn
-- statement:
--   The S3x3 construction uses the kpp hn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L379-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L379-L407

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]
variable [IsFractionRing o k0]
variable [IsLocalRing o]

theorem Formalism.FourierDecayAlt.P.S3x3.kpp_hn {r k : ℕ} {n : Matrix (Idx r k) (Idx r k) k0} {h : Matrix (Fin k) (Fin k) k0}
    (hn : IsN n) (hh : IsUnit h.det) :
    (∃ y : Matrix (Idx r k) (Idx r k) o, KppO y ∧ y.map (algebraMap o k0) = hEmb r h * n) ↔
      InGLo o n ∧ ∃ y : Matrix (Fin k) (Fin k) o, IsUnit y.det ∧
        IsUpUni (y.map (IsLocalRing.residue o)) ∧ y.map (algebraMap o k0) = h := by sorry
