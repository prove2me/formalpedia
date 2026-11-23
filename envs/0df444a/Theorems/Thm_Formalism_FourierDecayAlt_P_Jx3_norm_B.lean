-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_norm_B
-- name    : Formalism.FourierDecayAlt.P.Jx3.norm_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:38.217798+00:00
-- url     : https://prove2.me/theorems/2e875cd1-311d-4507-ad42-971963c6cfe9
-- title:
--   Jx3: norm B
-- statement:
--   The Jx3 construction uses the norm B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L216-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L216-L222

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3

theorem Formalism.FourierDecayAlt.P.Jx3.norm_B (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ)
    (hg : 0 < g) : (FractionalIdeal.absNorm (S6.idl E g 0 (-(ν + 1))) : ℝ) =
      ((S6.rd E ^ (-(ν + 1))) ^ S6.deg E) ^ 2 := by sorry
