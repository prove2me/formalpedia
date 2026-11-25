-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_sum_fibre
-- name    : Formalism.L2.Th1.C.sum_fibre
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:47:40.022932+00:00
-- url     : https://prove2.me/theorems/3ef18a1d-d1a7-4c42-b340-8843b14fcc58
-- title:
--   C: sum fibre
-- statement:
--   The C construction uses the sum fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/SecondCoeffConsistency.lean#L12-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/SecondCoeffConsistency.lean#L12-L38

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SecondCoeffConsistency
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem Formalism.L2.Th1.C.sum_fibre (fa : G →+ G) (wp : G → K) (al : K)
    (h : ∀ T, fa T ≠ 0 → al ^ 2 * wp (fa T) =
      wp T + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), (wp (T + P) - wp P))
    (T₀ : G) (hT₀ : fa T₀ ≠ 0) :
    ∑ T ∈ Finset.univ.filter (fun T => fa T = fa T₀), wp T =
      al ^ 2 * wp (fa T₀) + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), wp P := by sorry
