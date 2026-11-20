-- Prove2me | Theorems.Thm_EF104CandidateFamily__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- name    : EF104CandidateFamily__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T09:18:52.596875+00:00
-- url     : https://prove2.me/theorems/a6bd540b-6cfc-4764-9098-17828fcd9724
-- title:
--   Every guess has a record-independent greedy suffix profile
-- statement:
--   Each guess has a greedy allocation of sets independent of valid aligned records and choice oracles. Apply the proved trimming maximality theorem through the proved candidate-history rule to obtain the profile contract for each execution. Profiles for the same orders are equal by induction: equal earlier bundles give identical admissibility bounds, and mutual maximality gives equality of the next suffixes. Construct a reference valid record from 0, 1, and all participating piece endpoints, recording true cell values, then choose its outputs. This removes execution and record dependence from the parent. Empty pieces have only the empty suffix; zero-valued plateaus require maximality, not merely equality of values. The statement also permits empty N.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
import Theorems.Thm_EnvyFreeCake104_Divide_candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
open EnvyFreeCake104.Divide

theorem EF104CandidateFamily__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF) :
    ∃ C : (List ι × List ι) → ι → Set ℝ,
      ∀ g ∈ guesses N,
        EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V P g.1 g.2 (C g) ∧
        ∀ (t : Rec ι), t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
          ∀ q : ChoiceOracle ι,
            ∃ (Y : ι → Piece) (R : Piece) (u : Rec ι) (tr : List (Event ι)),
              exec V q (candidate N P g.1 g.2) t = some ((Y, R), u, tr) ∧
              ∀ i ∈ N, (Y i).toSet = C g i := by sorry
