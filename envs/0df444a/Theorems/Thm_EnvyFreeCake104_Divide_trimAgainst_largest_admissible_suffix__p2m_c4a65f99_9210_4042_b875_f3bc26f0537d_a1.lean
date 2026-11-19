-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
-- name    : EnvyFreeCake104.Divide.trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T18:36:46.589507+00:00
-- url     : https://prove2.me/theorems/e0d664ca-af16-41d5-85cd-aa65459b7f06
-- title:
--   Trimming retains the largest suffix satisfying all reference bounds
-- statement:
--   Assuming the parent's prefix-cut guarantee, trimming any well-formed aligned piece against participating agents with well-formed aligned reference bundles succeeds from every valid state and initial transcript. It extends the recorded points and returns a well-formed aligned suffix satisfying all reference bounds and containing every suffix satisfying those bounds. Every participating valuation respects this containment. The initial removed-piece accumulator is arbitrary.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
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
    (Y : ι → Piece) (hY : ∀ i ∈ N, (Y i).WF)
    (earlier : List ι) (hearlier : ∀ i ∈ earlier, i ∈ N)
    (Q removed : Piece) (hQ : Q.WF)
    (s : Rec ι) (hs : s.Valid V N)
    (hYs : ∀ i ∈ N, s.Aligned (Y i)) (hQs : s.Aligned Q)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    ∃ (B rem : Piece) (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((trimAgainst N Y earlier Q removed).run s) tr₀ =
        some (((B, rem), s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ B.WF ∧ s'.Aligned B ∧
      IsSuffix B.toSet Q ∧
      (∀ i ∈ earlier, (V i).value B.toSet ≤ (V i).value (Y i).toSet) ∧
      ∀ S : Set ℝ, IsSuffix S Q →
        (∀ i ∈ earlier, (V i).value S ≤ (V i).value (Y i).toSet) →
        S ⊆ B.toSet ∧ ∀ i ∈ N, (V i).value S ≤ (V i).value B.toSet := by sorry
