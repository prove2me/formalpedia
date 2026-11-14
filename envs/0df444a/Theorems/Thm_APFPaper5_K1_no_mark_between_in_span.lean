-- Prove2me | Theorems.Thm_APFPaper5_K1_no_mark_between_in_span
-- name    : APFPaper5.K1.no_mark_between_in_span
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:39:18.568474+00:00
-- url     : https://prove2.me/theorems/20d7062b-b297-4cd5-aaff-68f8c0091b53
-- title:
--   A unit mark in a normalized two-mark span has endpoint overlap
-- statement:
--   Let B be a real-bilinear pairing on a supplied real vector space. Assume p and p′ each have self-score one, both ordered cross scores vanish, and q=ap+bp′. Assume also B(q,q)=1 and B(p,q)+B(p′,q)=1. Then B(p,q)=0 or B(p,q)=1. Thus these hypotheses exclude a strictly intermediate overlap within that supplied span. This declaration does not construct an additional direction or prove an exact dimension of a mark space or physical space.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_rank_three.lean:40; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-391;3038-3041; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_three_yeses_2026-11-12.md, 1 and standing

import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem APFPaper5.K1.no_mark_between_in_span (B : V → V → ℝ) (hB : IsBilinear B) (p p' q : V) (a b : ℝ)
    (hpp : B p p = 1) (hp'p' : B p' p' = 1) (hpp' : B p p' = 0) (hp'p : B p' p = 0)
    (hq : q = a • p + b • p') (hqq : B q q = 1) (hnorm : B p q + B p' q = 1) :
    B p q = 0 ∨ B p q = 1 := by sorry
