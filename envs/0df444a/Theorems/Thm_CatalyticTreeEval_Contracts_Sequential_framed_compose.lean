-- Prove2me | Theorems.Thm_CatalyticTreeEval_Contracts_Sequential_framed_compose
-- name    : CatalyticTreeEval.Contracts.Sequential.framed_compose
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T01:45:52.5322+00:00
-- url     : https://prove2.me/theorems/59f16754-87c8-45fb-9d23-ce8000d1ddf2
-- title:
--   Native sequential composition preserves full execution invariants
-- statement:
--   The native finite binary sequential machine runs the first machine to its first halt, then runs the second on the same tapes, heads and output. Exact times add. Any invariant proved for the embedded first phase and for the time-shifted second phase holds throughout the actual composite execution, including both endpoints. Failed native transitions remain failures.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section3.1 and Lemma4.5. Native sequencing uses the standard halting-redirection construction.

import Definitions.Def_CatalyticTreeEval_SequentialMachine
open CatalyticTreeEval.Contracts CatalyticTreeEval.Contracts.Sequential CatalyticMatching.General
set_option autoImplicit false

theorem CatalyticTreeEval.Contracts.Sequential.framed_compose (A B : Machine) (input : List Bool)
    {c a : Configuration A} {b : Configuration B} {s t : ℕ}
    {IA : ℕ → Configuration A → Prop} {IB : ℕ → Configuration B → Prop}
    {I : ℕ → Configuration (machine A B) → Prop}
    (HA : Segment (A.step input) IA c a s)
    (HB : Segment (B.step input) IB (handoff A B a) b t)
    (halt : a.state = none)
    (live : ∀ u < s, ∀ d, runFrom (A.step input) c u = some d → d.state ≠ none)
    (hA : ∀ u ≤ s, ∀ d, IA u d → I u (leftConfig A B d))
    (hB : ∀ u ≤ t, ∀ d, IB u d → I (s + u) (rightConfig A B d)) :
    Segment ((machine A B).step input) I (leftConfig A B c) (rightConfig A B b) (s + t) := by sorry
