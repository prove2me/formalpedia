-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_candidate_greedy_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
-- name    : EnvyFreeCake104.Divide.candidate_greedy_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T18:28:52.396788+00:00
-- url     : https://prove2.me/theorems/c4a65f99-9210-4042-b875-f3bc26f0537d
-- title:
--   Prefix-cut guarantees imply greedy candidate maximality
-- statement:
--   Assuming the explicit universal prefix-cut guarantee hcut, candidate construction succeeds whenever the agent list has no repetitions and every zipped pair belongs to N. At each assignment, its output contains every suffix of the original assigned piece satisfying the earlier agents’ value bounds, and every participating valuation values that suffix no more than the output bundle. No envy-freeness, equal list lengths, or pairwise disjointness is assumed.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.candidate_greedy_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hcut : ∀ (i : ι) (hi : i ∈ N) (Q : Piece) (hQ : Q.WF)
    (s : Rec ι) (hs : s.Valid V N) (hQs : s.Aligned Q)
    (w : ℝ) (hw : 0 ≤ w) (hwQ : w ≤ (V i).value Q.toSet)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
    ∃ (p : Pos) (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((prefixCut N i Q w).run s) tr₀ = some ((p, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧
      (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
      s'.Aligned (prefixList Q p) ∧ s'.Aligned (suffixList Q p) ∧
      (V i).value (prefixList Q p).toSet = w ∧
      (V i).value (suffixList Q p).toSet = (V i).value Q.toSet - w ∧
      IsSuffix (suffixList Q p).toSet Q ∧
      ∀ S : Set ℝ, IsSuffix S Q →
        (V i).value S ≤ (V i).value Q.toSet - w →
        S ⊆ (suffixList Q p).toSet)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (ag pc : List ι) (hag : ag.Nodup)
    (hmem : ∀ p ∈ ag.zip pc, p.1 ∈ N ∧ p.2 ∈ N) (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (candidate N P ag pc) s = some ((Y, R), s', tr) ∧
      ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
        ag.zip pc = before ++ p :: after →
        ∀ S : Set ℝ, IsSuffix S (P p.2) →
          (∀ q ∈ before, (V q.1).value S ≤ (V q.1).value (Y q.1).toSet) →
          S ⊆ (Y p.1).toSet ∧
          ∀ i ∈ N, (V i).value S ≤ (V i).value (Y p.1).toSet := by sorry
