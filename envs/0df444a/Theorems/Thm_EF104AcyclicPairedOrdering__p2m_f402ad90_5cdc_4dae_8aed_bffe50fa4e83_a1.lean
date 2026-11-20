-- Prove2me | Theorems.Thm_EF104AcyclicPairedOrdering__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1
-- name    : EF104AcyclicPairedOrdering__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T15:03:24.396436+00:00
-- url     : https://prove2.me/theorems/58bb257d-915f-496b-9c96-8499c03b027a
-- title:
--   An acyclic relation admits paired permutation orders with earlier predecessors
-- statement:
--   A permutation preserving a finite set and an acyclic relation admit paired orders among guesses, with pieces following the permutation and every vertex having an incoming edge from the set having an earlier predecessor.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
open EnvyFreeCake104.Divide

theorem EF104AcyclicPairedOrdering__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1
    {ι : Type} [DecidableEq ι] (N : Finset ι) (σ : Equiv.Perm ι)
    (hσ : ∀ i, i ∈ N ↔ σ i ∈ N) (R : ι → ι → Prop)
    (hacyc : ∀ i, ¬ Relation.TransGen R i i) :
    ∃ g ∈ guesses N,
      (∀ p ∈ g.1.zip g.2, p.1 ∈ N ∧ p.2 = σ p.1) ∧
      ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
        g.1.zip g.2 = before ++ p :: after →
        (∃ i ∈ N, R i p.1) → ∃ q ∈ before, R q.1 p.1 := by sorry
