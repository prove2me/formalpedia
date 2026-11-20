-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_uniform_envy_free_guess__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
-- name    : EnvyFreeCake104.Divide.uniform_envy_free_guess__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T07:02:54.429778+00:00
-- url     : https://prove2.me/theorems/e30dcdf5-697c-4dac-9565-d07a1e730ebe
-- title:
--   A fixed ordering pair yields an envy-free candidate from every valid refinement
-- statement:
--   For nonempty N and pairwise disjoint well-formed pieces P, one guess produces an envy-free candidate from every valid aligned record state, under every choice oracle. No positivity or normalization is assumed.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_claim_7
open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.uniform_envy_free_guess__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet) :
    ∃ g ∈ guesses N,
      ∀ (t : Rec ι), t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
        ∀ q : ChoiceOracle ι,
          ∃ (Y : ι → Piece) (R : Piece) (u : Rec ι) (tr : List (Event ι)),
            exec V q (candidate N P g.1 g.2) t = some ((Y, R), u, tr) ∧
            EnvyFree V N (fun i ↦ (Y i).toSet) := by sorry
