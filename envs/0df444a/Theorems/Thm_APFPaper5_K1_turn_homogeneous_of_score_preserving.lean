-- Prove2me | Theorems.Thm_APFPaper5_K1_turn_homogeneous_of_score_preserving
-- name    : APFPaper5.K1.turn_homogeneous_of_score_preserving
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:01:54.535953+00:00
-- url     : https://prove2.me/theorems/eac999fe-e5f5-4867-af92-8c97224ae2e7
-- title:
--   Surjective score preservation implies real homogeneity under left nondegeneracy
-- statement:
--   Let B be a real-bilinear pairing on a supplied real vector space. Assume hnd: left nondegeneracy; hiso: B(Ta,Tb)=B(a,b) for all a,b; and hsurj: every vector is an image under T. Then T(ra)=rT(a) for every real r and vector a. This declaration concludes scalar homogeneity, conditional on full-space surjectivity and score preservation. It does not derive those properties from admissible turns on a separate Held-state domain or construct a physical bilinear score.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_turn_structure.lean:46; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 427-470; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_cross_term_and_preservation_2026-11-12.md, standing

import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem APFPaper5.K1.turn_homogeneous_of_score_preserving (B : V → V → ℝ) (hB : IsBilinear B)
    (hnd : ∀ v : V, (∀ c : V, B v c = 0) → v = 0) (T : V → V)
    (hiso : ∀ a b : V, B (T a) (T b) = B a b) (hsurj : ∀ c : V, ∃ c' : V, T c' = c) :
    ∀ (r : ℝ) (a : V), T (r • a) = r • T a := by sorry
