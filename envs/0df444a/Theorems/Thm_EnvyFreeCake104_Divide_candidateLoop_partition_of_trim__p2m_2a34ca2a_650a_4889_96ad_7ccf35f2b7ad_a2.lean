-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_candidateLoop_partition_of_trim__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2
-- name    : EnvyFreeCake104.Divide.candidateLoop_partition_of_trim__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T15:27:49.386782+00:00
-- url     : https://prove2.me/theorems/eb7e1d22-52e9-4906-a9bc-6d473b544900
-- title:
--   Candidate-loop conservation follows from a local trimming partition contract
-- statement:
--   Assuming local trimming conservation, successfully processing distinct participating agents paired with every input piece exactly once partitions the input union into residue and allocated cake, for every initial transcript and adaptive choice oracle.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.candidateLoop_partition_of_trim__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (htrim : ∀ (A : ι → Piece) (hA : ∀ i ∈ N, (A i).WF)
      (earlier : List ι) (hearlier : ∀ i ∈ earlier, i ∈ N)
      (Q : Piece) (hQ : Q.WF) (t : Rec ι) (ht : t.Valid V N)
      (hAt : ∀ i ∈ N, t.Aligned (A i)) (hQt : t.Aligned Q)
      (o : ChoiceOracle ι) (tr₀ : List (Event ι))
      (B rem : Piece) (t' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((trimAgainst N A earlier Q []).run t) tr₀ =
        some (((B, rem), t'), tr) →
      t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ B.WF ∧ t'.Aligned B ∧
        Disjoint B.toSet rem.toSet ∧ B.toSet ∪ rem.toSet = Q.toSet)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j →
      Disjoint (P i).toSet (P j).toSet)
    (pairs : List (ι × ι))
    (hag : (pairs.map Prod.fst).Nodup)
    (hagents : ∀ q ∈ pairs, q.1 ∈ N)
    (hpieces : (pairs.map Prod.snd).Perm N.toList)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o
      ((candidateLoop N P pairs [] (fun _ ↦ []) []).run s) tr₀ =
        some (((Y, R), s'), tr)) :
    R.toSet ∪ (⋃ i ∈ N, (Y i).toSet) = (⋃ i ∈ N, (P i).toSet) ∧
      Disjoint R.toSet (⋃ i ∈ N, (Y i).toSet) := by sorry
