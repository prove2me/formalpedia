-- Prove2me | Theorems.Thm_Formalism_GM_TM_finrank_of_lattice_basis
-- name    : Formalism.GM.TM.finrank_of_lattice_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:50.500238+00:00
-- url     : https://prove2.me/theorems/cc604ff3-bb63-4a05-9f72-55c86f249e6f
-- title:
--   TM: finrank of lattice basis
-- statement:
--   The TM construction uses the finrank of lattice basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L110-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L110-L132

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
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.GM.TM.finrank_of_lattice_basis {σ : Type} (S : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) {n₀ : ℕ}
    (f : Fin n₀ → MvPolynomial σ ℚ_[p]) (hli : LinearIndependent ℤ_[p] f)
    (hsp : Submodule.span ℤ_[p] (Set.range f) = S.restrictScalars ℤ_[p] ⊓ IntPol p σ) :
    Module.finrank ℚ_[p] S = n₀ := by sorry
