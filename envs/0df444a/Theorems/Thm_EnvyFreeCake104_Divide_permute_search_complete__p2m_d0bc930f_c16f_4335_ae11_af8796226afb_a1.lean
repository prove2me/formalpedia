-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_permute_search_complete__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
-- name    : EnvyFreeCake104.Divide.permute_search_complete__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T07:02:51.786365+00:00
-- url     : https://prove2.me/theorems/5ac6660c-15c5-4a5b-8ff4-66bb612ae8d9
-- title:
--   A persistent successful guess makes exhaustive Permute search complete with its cut budget
-- statement:
--   Given a persistent envy-free guess, Permute succeeds envy-free within the stated prefix-cut budget. Its result is the output of a candidate for an actual guess, started from valid aligned intermediate records with a shifted choice oracle.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.permute_search_complete__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (hgood : ∃ g ∈ guesses N,
      ∀ (t : Rec ι), t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
        ∀ q : ChoiceOracle ι,
          ∃ (Y : ι → Piece) (R : Piece) (u : Rec ι) (tr : List (Event ι)),
            exec V q (candidate N P g.1 g.2) t = some ((Y, R), u, tr) ∧
            EnvyFree V N (fun i ↦ (Y i).toSet))
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (permute N P) s = some ((Y, R), s', tr) ∧
      EnvyFree V N (fun i ↦ (Y i).toSet) ∧
      s'.prefixCuts ≤ s.prefixCuts + N.card.choose 2 * (N.card.factorial) ^ 2 ∧
      ∃ (g : List ι × List ι) (t : Rec ι) (q : ChoiceOracle ι)
        (tc : List (Event ι)),
        g ∈ guesses N ∧ t.Valid V N ∧ (∀ i ∈ N, t.Aligned (P i)) ∧
        exec V q (candidate N P g.1 g.2) t = some ((Y, R), s', tc) := by sorry
