-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_endpoint_recording__p2m_8c415f54_233a_4754_8600_5f90a07d6713_a1
-- name    : EnvyFreeCake104.Divide.prefixCut_endpoint_recording__p2m_8c415f54_233a_4754_8600_5f90a07d6713_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T01:31:21.870257+00:00
-- url     : https://prove2.me/theorems/9b8f1de4-1ca8-4e82-a2d5-046493ddc8fb
-- title:
--   Local answer safety implies successful prefix-cut execution and endpoint recording
-- statement:
--   Assume splitting preserves valid records, every interval start is recorded, and each successful positive-residual cell search produces a recorded cell whose cut answer is either already recorded or strictly interior to that cell. Every successful pure selection is then realized by prefixCut, preserving validity, extending the recorded points, and recording the returned endpoint whenever its index is in range. This holds for arbitrary requests, pieces, choice oracles, and initial transcripts.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

theorem EnvyFreeCake104.Divide.prefixCut_endpoint_recording__p2m_8c415f54_233a_4754_8600_5f90a07d6713_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hsplit : ∀ (t : Rec ι), t.Valid V N →
      ∀ (c y : ℝ), c ∈ t.pts → c < y → y < t.nextPt c →
      ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((splitCell N c y).run t) tr₀ = some (((), t'), tr) ∧
        t'.Valid V N ∧ t'.pts = insert y t.pts)
    (i : ι) (Q : Piece) (s : Rec ι) (hs : s.Valid V N)
    (hstarts : ∀ I ∈ Q, I.a ∈ s.pts)
    (hsafe : ∀ I ∈ Q, ∀ (r : ℝ), 0 < r → ∀ (c t : ℝ),
      findCell s i
        ((s.pts.filter (fun c => I.a ≤ c ∧ c < I.b)).sort (· ≤ ·)) r =
          some (c, t) →
      c ∈ s.pts ∧
        (cutAnswer V i c t ∈ s.pts ∨
          (c < cutAnswer V i c t ∧ cutAnswer V i c t < s.nextPt c)))
    (w : ℝ) (p : Pos)
    (hp : (match findInterval s i Q 0 w with
        | none => if w ≤ 0 then some (Q.length, (0 : ℝ)) else none
        | some (k, r) =>
          if r ≤ 0 then some (k, (Q.getD k default).a)
          else
            match findCell s i
                ((s.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
                  c < (Q.getD k default).b)).sort (· ≤ ·)) r with
            | none => none
            | some (c, t) => some (k, cutAnswer V i c t)) = some p)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    ∃ (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((prefixCut N i Q w).run s) tr₀ = some ((p, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧
      (p.1 < Q.length → p.2 ∈ s'.pts) := by sorry
