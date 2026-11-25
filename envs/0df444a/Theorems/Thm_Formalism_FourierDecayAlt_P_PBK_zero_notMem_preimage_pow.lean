-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_zero_notMem_preimage_pow
-- name    : Formalism.FourierDecayAlt.P.PBK.zero_notMem_preimage_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:20.634928+00:00
-- url     : https://prove2.me/theorems/b9e047e1-4f82-42da-aad7-0e411aa1b57b
-- title:
--   PBK: zero not Mem preimage pow
-- statement:
--   The PBK construction uses the zero not Mem preimage pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L60-L64

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.PBK.zero_notMem_preimage_pow {s : ℕ} (hs : s ≠ 0) (ε : ℂ) {Q : Set ℂ} (h0 : (0 : ℂ) ∉ Q) :
    (0 : ℂ) ∉ {z : ℂ | ε⁻¹ * z ^ s ∈ Q} := by sorry
