-- Prove2me | Theorems.Thm_Formalism_ELL_Lemma2Aux_choose_pow_mul_modEq
-- name    : Formalism.ELL.Lemma2Aux.choose_pow_mul_modEq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:32.912244+00:00
-- url     : https://prove2.me/theorems/0d5f7054-a12e-45e6-b515-91f55fea7efc
-- title:
--   Lemma2 Aux: choose pow mul mod Eq
-- statement:
--   The Lemma2 Aux construction uses the choose pow mul mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L34-L42

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CoefficientWeightsLemmaTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.Lemma2Aux
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.Lemma2Aux.choose_pow_mul_modEq {p : ℕ} (hp : p.Prime) (k m : ℕ) :
    (p ^ k * m).choose (p ^ k) ≡ m [MOD p] := by sorry
