-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_separated_sum_le_prod_integrals
-- name    : Formalism.HermitianLatticeCounting.P.separated_sum_le_prod_integrals
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:15.196376+00:00
-- url     : https://prove2.me/theorems/7f6cd151-d2c8-402a-b564-64a757484889
-- title:
--   P: separated sum le prod integrals
-- statement:
--   The P construction uses the separated sum le prod integrals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L196-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L196-L226

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.separated_sum_le_prod_integrals (hd : SeparatedPolydiscsDisjoint) {ι : Type} [Fintype ι] (ro : ℝ) (S : Finset (ι → ℂ)) (hro : 0 < ro)
    (hS : IsNormSeparated ro S) (φ ψ : ι → ℂ → ℝ) (hψ : ∀ v z, 0 ≤ ψ v z)
    (hφ : ∀ v z, 0 ≤ φ v z)
    (hint : ∀ v, Integrable (ψ v)) (hcmp : ∀ v D x, ‖x - D‖ < ro / 2 → φ v D ≤ ψ v x) :
    (∑ D ∈ S, ∏ v, φ v (D v)) * (π * (ro / 2) ^ 2) ^ Fintype.card ι ≤ ∏ v, ∫ x, ψ v x := by sorry
