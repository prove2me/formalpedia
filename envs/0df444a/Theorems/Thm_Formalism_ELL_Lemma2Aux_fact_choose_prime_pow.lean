-- Prove2me | Theorems.Thm_Formalism_ELL_Lemma2Aux_fact_choose_prime_pow
-- name    : Formalism.ELL.Lemma2Aux.fact_choose_prime_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:08.056266+00:00
-- url     : https://prove2.me/theorems/2b139abd-a673-4c06-9ab4-3d1aec05c980
-- title:
--   Lemma2 Aux: fact choose prime pow
-- statement:
--   The Lemma2 Aux construction uses the fact choose prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L44-L50

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

theorem Formalism.ELL.Lemma2Aux.fact_choose_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) :
    ((p ^ k).choose (p ^ (k - 1))).factorization p = 1 := by sorry
