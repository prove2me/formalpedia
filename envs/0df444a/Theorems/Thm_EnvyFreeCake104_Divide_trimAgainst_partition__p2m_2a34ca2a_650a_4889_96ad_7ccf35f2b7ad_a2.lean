-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_trimAgainst_partition__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2
-- name    : EnvyFreeCake104.Divide.trimAgainst_partition__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T15:27:54.254872+00:00
-- url     : https://prove2.me/theorems/c66a0ab9-5f8e-42b0-a2fb-46a2b76a127c
-- title:
--   Successful trimming partitions its input and preserves geometric record invariants
-- statement:
--   Trimming a well-formed aligned piece against participating agents preserves valid records and recorded endpoints, and returns disjoint retained and removed sets whose union is the original piece.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.trimAgainst_partition__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) :
    ∀ (A : ι → Piece) (hA : ∀ i ∈ N, (A i).WF)
      (earlier : List ι) (hearlier : ∀ i ∈ earlier, i ∈ N)
      (Q : Piece) (hQ : Q.WF) (t : Rec ι) (ht : t.Valid V N)
      (hAt : ∀ i ∈ N, t.Aligned (A i)) (hQt : t.Aligned Q)
      (o : ChoiceOracle ι) (tr₀ : List (Event ι))
      (B rem : Piece) (t' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((trimAgainst N A earlier Q []).run t) tr₀ =
        some (((B, rem), t'), tr) →
      t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ B.WF ∧ t'.Aligned B ∧
        Disjoint B.toSet rem.toSet ∧ B.toSet ∪ rem.toSet = Q.toSet := by sorry
