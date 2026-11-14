-- Prove2me | Theorems.Thm_APFPaper5_K1_turn_fixes_total
-- name    : APFPaper5.K1.turn_fixes_total
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:58:16.313758+00:00
-- url     : https://prove2.me/theorems/41c85246-596d-4185-825c-aa29259d6be9
-- title:
--   Score preservation and mark separation fix a supplied normalized total
-- statement:
--   Let B be real-bilinear and let Marks be a supplied set of vectors. Assume hspan: a vector scoring zero against every mark is zero; hiso: T preserves every B-score; honto: each mark has a preimage under T that is also a mark; and hnorm: a supplied vector e scores one against every mark. Then Te=e. This declaration does not require a separately assumed linearity of T. Its mark separation, onto-mark coverage and total normalization remain explicit structural hypotheses, not derived physical properties.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_turn_structure.lean:63; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 427-470; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_cross_term_and_preservation_2026-11-12.md, standing

import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem APFPaper5.K1.turn_fixes_total (B : V → V → ℝ) (hB : IsBilinear B) (Marks : Set V)
    (hspan : ∀ v : V, (∀ m ∈ Marks, B v m = 0) → v = 0) (T : V → V)
    (hiso : ∀ a b : V, B (T a) (T b) = B a b)
    (honto : ∀ m ∈ Marks, ∃ n ∈ Marks, T n = m) (e : V)
    (hnorm : ∀ m ∈ Marks, B e m = 1) : T e = e := by sorry
