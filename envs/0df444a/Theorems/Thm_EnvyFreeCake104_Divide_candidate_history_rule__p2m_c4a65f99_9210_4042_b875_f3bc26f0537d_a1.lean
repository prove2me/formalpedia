-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
-- name    : EnvyFreeCake104.Divide.candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T18:36:45.219413+00:00
-- url     : https://prove2.me/theorems/8a7f91d3-630e-4699-950d-8a04643e5004
-- title:
--   Candidate iteration preserves abstract contracts depending on earlier bundles
-- statement:
--   Let K be any local assignment predicate whose reference-allocation dependence is restricted to earlier agents. If every trimming call succeeds, preserves valid records and alignment through point extension, returns a well-formed bundle, and establishes K, then candidate construction succeeds and establishes K at every assignment relative to its final allocation. Only agent-list uniqueness and membership of zipped pairs are required.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (K : List ι → (ι → Piece) → Piece → Piece → Prop)
    (hstable : ∀ (earlier : List ι) (Y Z : ι → Piece) (Q B : Piece),
      (∀ i ∈ earlier, Y i = Z i) → K earlier Y Q B → K earlier Z Q B)
    (htrim : ∀ (Y : ι → Piece) (earlier : List ι) (Q : Piece) (s : Rec ι),
      (∀ i ∈ N, (Y i).WF) → (∀ i ∈ earlier, i ∈ N) →
      Q.WF → s.Valid V N →
      (∀ i ∈ N, s.Aligned (Y i)) → s.Aligned Q →
      ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (B rem : Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((trimAgainst N Y earlier Q []).run s) tr₀ =
          some (((B, rem), s'), tr) ∧
        s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ B.WF ∧ s'.Aligned B ∧ K earlier Y Q B)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (ag pc : List ι) (hag : ag.Nodup)
    (hmem : ∀ p ∈ ag.zip pc, p.1 ∈ N ∧ p.2 ∈ N) (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (candidate N P ag pc) s = some ((Y, R), s', tr) ∧
      ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
        ag.zip pc = before ++ p :: after →
        K (before.map Prod.fst) Y (P p.2) (Y p.1) := by sorry
