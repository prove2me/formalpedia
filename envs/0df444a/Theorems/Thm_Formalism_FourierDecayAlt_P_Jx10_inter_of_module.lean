-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx10_inter_of_module
-- name    : Formalism.FourierDecayAlt.P.Jx10.inter_of_module
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:57.676944+00:00
-- url     : https://prove2.me/theorems/bb76d5c5-a7b3-4b04-8647-f05b1c3a1ac4
-- title:
--   Jx10: inter of module
-- statement:
--   The Jx10 construction uses the inter of module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevToThreshold.lean#L40-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevToThreshold.lean#L40-L64

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx10

theorem Formalism.FourierDecayAlt.P.Jx10.inter_of_module (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E)
    (hL : ∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
      algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) (t : E)
    (h : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ S6.locAt E P L) : t ∈ L := by sorry
