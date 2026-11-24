-- Prove2me | Theorems.Thm_Formalism_GM_badCrit_pairs
-- name    : Formalism.GM.badCrit_pairs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:36.40281+00:00
-- url     : https://prove2.me/theorems/a881d62c-ff59-4207-a5cd-8b755977d7b8
-- title:
--   GM: bad Crit pairs
-- statement:
--   The GM construction uses the bad Crit pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L111-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L111-L217

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

theorem Formalism.GM.badCrit_pairs (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L L₁ : Submodule ℤ_[p] Vs) (D : ℤ)
    [Module.Finite ℤ_[p] L] (hle : L₁ ≤ L)
    (hprim : ∀ u ∈ L₁, (∀ (a : ℤ_[p]) (x : Vs), x ∈ L₁ → u = a • x → IsUnit a) →
      ∃ u' ∈ L, (p : ℝ) ^ (-D) ≤ ‖be u u'‖) :
    ∃ x y : Fin (Module.finrank ℤ_[p] L₁) → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0 := by sorry
