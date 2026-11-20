-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_equalCuts_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
-- name    : EnvyFreeCake104.Divide.equalCuts_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T06:58:13.269681+00:00
-- url     : https://prove2.me/theorems/c286858a-9e65-4696-8505-9d74071d7a32
-- title:
--   Repeated equal prefix cuts form an aligned partition with linear query overhead
-- statement:
--   For a participating cutter, m equal prefix cuts of a well-formed aligned piece succeed, preserve valid records, and produce m+1 aligned, pairwise disjoint pieces covering the original piece, each of value V_c(Q)/(m+1). At most m(N.card+1) queries are issued, including when Q is empty or has zero value.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.6, Lemma 3 (restated p.10)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.equalCuts_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (c : ι) (hc : c ∈ N) (m : ℕ) (Q : Piece) (hQ : Q.WF)
    (s : Rec ι) (hs : s.Valid V N) (hQs : s.Aligned Q) (o : ChoiceOracle ι) :
    ∃ (ps : List Piece) (s₁ : Rec ι) (tr₁ : List (Event ι)),
      exec V o (equalCuts N c ((V c).value Q.toSet / ((m + 1 : ℕ) : ℝ)) m Q) s =
        some (ps, s₁, tr₁) ∧
      s₁.Valid V N ∧ ps.length = m + 1 ∧
      (∀ P ∈ ps, P.WF) ∧ (∀ P ∈ ps, s₁.Aligned P) ∧
      ps.Pairwise (fun P R ↦ Disjoint P.toSet R.toSet) ∧
      (⋃ P ∈ ps, P.toSet) = Q.toSet ∧
      (∀ P ∈ ps, (V c).value P.toSet = (V c).value Q.toSet / ((m + 1 : ℕ) : ℝ)) ∧
      queryCount tr₁ ≤ m * (N.card + 1) := by sorry
