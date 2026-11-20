-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_assign_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
-- name    : EnvyFreeCake104.Divide.assign_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T06:58:00.53419+00:00
-- url     : https://prove2.me/theorems/3d245ed7-e7ef-4932-be64-c4d1b3593bc7
-- title:
--   Assigning a partition list to distinct agents preserves its properties
-- statement:
--   Assigning an equally long partition list to the duplicate-free list of agents preserves well-formedness, alignment, disjointness, coverage, and common value. The statement also covers an empty agent set.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.6, Lemma 3 (restated p.10)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.assign_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
    {ι : Type} [DecidableEq ι] (N : Finset ι) (ps : List Piece)
    (hlen : ps.length = N.card) (s : Rec ι) (v : Valuation) (w : ℝ) (Q : Set ℝ)
    (hwf : ∀ P ∈ ps, P.WF) (halign : ∀ P ∈ ps, s.Aligned P)
    (hdis : ps.Pairwise (fun P R ↦ Disjoint P.toSet R.toSet))
    (hcover : (⋃ P ∈ ps, P.toSet) = Q) (hval : ∀ P ∈ ps, v.value P.toSet = w) :
    (∀ i ∈ N, (assign N.toList ps i).WF) ∧
    (∀ i ∈ N, s.Aligned (assign N.toList ps i)) ∧
    (∀ i ∈ N, ∀ j ∈ N, i ≠ j →
      Disjoint (assign N.toList ps i).toSet (assign N.toList ps j).toSet) ∧
    (⋃ i ∈ N, (assign N.toList ps i).toSet) = Q ∧
    (∀ i ∈ N, v.value (assign N.toList ps i).toSet = w) := by sorry
