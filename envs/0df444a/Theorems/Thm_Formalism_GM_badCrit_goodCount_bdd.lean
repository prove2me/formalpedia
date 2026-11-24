-- Prove2me | Theorems.Thm_Formalism_GM_badCrit_goodCount_bdd
-- name    : Formalism.GM.badCrit_goodCount_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:00.230311+00:00
-- url     : https://prove2.me/theorems/9e3c8dba-1b08-4d7f-b167-b074b1dfa2df
-- title:
--   GM: bad Crit good Count bdd
-- statement:
--   The GM construction uses the bad Crit good Count bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L88-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L88-L103

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module
variable {p : ℕ} [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]

theorem Formalism.GM.badCrit_goodCount_bdd (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ)
    [Module.Finite ℤ_[p] L] :
    BddAbove {n | ∃ x y : Fin n → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0} := by sorry
