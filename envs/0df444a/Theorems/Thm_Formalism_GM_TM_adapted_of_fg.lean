-- Prove2me | Theorems.Thm_Formalism_GM_TM_adapted_of_fg
-- name    : Formalism.GM.TM.adapted_of_fg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:47.321718+00:00
-- url     : https://prove2.me/theorems/796f62e1-d6db-4257-879b-58063680bdb3
-- title:
--   TM: adapted of fg
-- statement:
--   The TM construction uses the adapted of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L485-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L485-L509

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.GM.TM.adapted_of_fg (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (hFG : L.FG) (D : ℕ)
    (hD : ∀ x ∈ L, ∀ m ∈ x.support, m v ≤ D) :
    ∃ (n₀ : ℕ) (f : Fin n₀ → MvPolynomial σ ℚ_[p]) (ord : Fin n₀ → ℕ),
      LinearIndependent ℤ_[p] f ∧ Submodule.span ℤ_[p] (Set.range f) = L ∧
      (∀ b, HasOrder v (ord b) (f b)) ∧ ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = filL L v e := by sorry
