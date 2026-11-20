-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_core_equal_partition__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
-- name    : EnvyFreeCake104.Divide.core_equal_partition__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T06:47:21.162515+00:00
-- url     : https://prove2.me/theorems/7c833f14-cb58-4a57-947b-39a2d0559683
-- title:
--   Core’s equal partition and transfer to its Permute continuation
-- statement:
--   Core’s initial stage produces a valid aligned partition into cutter-equal pieces. Every successful Permute continuation under a shifted oracle lifts to the original Core execution, with at most (n−1)(n+1) additional queries. Empty cakes and zero cutter-value are permitted.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.6, Lemma 3 (restated p.10)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.core_equal_partition__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (c : ι) (hc : c ∈ N) (C : Piece) (hC : C.WF)
    (s : Rec ι) (hs : s.Valid V N) (hCs : s.Aligned C) (o : ChoiceOracle ι) :
    ∃ (P : ι → Piece) (s₁ : Rec ι) (o₁ : ChoiceOracle ι),
      s₁.Valid V N ∧
      (∀ i ∈ N, (P i).WF) ∧
      (∀ i ∈ N, s₁.Aligned (P i)) ∧
      (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet) ∧
      (⋃ i ∈ N, (P i).toSet) = C.toSet ∧
      (∀ i ∈ N, (V c).value (P i).toSet = (V c).value C.toSet / (N.card : ℝ)) ∧
      ∀ (Y : ι → Piece) (U : Piece) (s₂ : Rec ι) (tr₂ : List (Event ι)),
        exec V o₁ (permute N P) s₁ = some ((Y, U), s₂, tr₂) →
        ∃ tr : List (Event ι),
          exec V o (core N c C) s = some ((Y, U), s₂, tr) ∧
          queryCount tr ≤ (N.card - 1) * (N.card + 1) + queryCount tr₂ := by sorry
