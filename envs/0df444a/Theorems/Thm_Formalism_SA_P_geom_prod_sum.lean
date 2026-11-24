-- Prove2me | Theorems.Thm_Formalism_SA_P_geom_prod_sum
-- name    : Formalism.SA.P.geom_prod_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:47.801179+00:00
-- url     : https://prove2.me/theorems/4bd6de30-aaf7-4b6e-80f1-9d2b74017c6c
-- title:
--   P: geom prod sum
-- statement:
--   The P construction uses the geom prod sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L247-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean#L247-L269

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]

theorem Formalism.SA.P.geom_prod_sum {ι : Type} [Fintype ι] (T : Finset (ι → ℕ)) :
    ∑ k ∈ T, ∏ i, (1 / 2 : ℝ) ^ (k i) ≤ 2 ^ Fintype.card ι := by sorry
