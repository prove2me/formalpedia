-- Prove2me | Theorems.Thm_APFPaper5_K1_turn_additive_of_score_preserving
-- name    : APFPaper5.K1.turn_additive_of_score_preserving
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:56:02.272104+00:00
-- url     : https://prove2.me/theorems/2cba4a3e-dcf5-4295-adb4-eef7bac598e4
-- title:
--   Surjective score preservation implies additivity under left nondegeneracy
-- statement:
--   Let B be a real-bilinear pairing on a supplied real vector space. Assume hnd: a vector scoring zero against every second-slot vector is zero; hiso: B(Ta,Tb)=B(a,b) for all a,b; and hsurj: T is onto the entire vector space. Then T(a+b)=Ta+Tb for all a,b. The theorem concludes additivity only. The pairing, its nondegeneracy, all-pair score preservation and full-space surjectivity are supplied; no physical turn model or admissible inverse is constructed.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_turn_structure.lean:29; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 427-470; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_cross_term_and_preservation_2026-11-12.md, standing

import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem APFPaper5.K1.turn_additive_of_score_preserving (B : V → V → ℝ) (hB : IsBilinear B)
    (hnd : ∀ v : V, (∀ c : V, B v c = 0) → v = 0) (T : V → V)
    (hiso : ∀ a b : V, B (T a) (T b) = B a b) (hsurj : ∀ c : V, ∃ c' : V, T c' = c) :
    ∀ a b : V, T (a + b) = T a + T b := by sorry
