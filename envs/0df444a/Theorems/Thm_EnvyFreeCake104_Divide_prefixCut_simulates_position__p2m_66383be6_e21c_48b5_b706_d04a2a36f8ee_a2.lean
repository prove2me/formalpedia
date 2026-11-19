-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_simulates_position__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- name    : EnvyFreeCake104.Divide.prefixCut_simulates_position__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T19:01:33.655838+00:00
-- url     : https://prove2.me/theorems/8c415f54-233a-4754-8600-5f90a07d6713
-- title:
--   Stateful prefix cutting realizes the pure selector and preserves aligned records
-- statement:
--   Assuming splitting preservation and the local cut contract, every successful pure selection with nonnegative request is realized by prefixCut, preserving valid extending records and aligning both output pieces.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.prefixCut_simulates_position__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hsplit : ∀ (t : Rec ι), t.Valid V N →
      ∀ (c y : ℝ), c ∈ t.pts → c < y → y < t.nextPt c →
      ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((splitCell N c y).run t) tr₀ = some (((), t'), tr) ∧
        t'.Valid V N ∧ t'.pts = insert y t.pts)
    (i : ι) (hi : i ∈ N)
    (hcut : ∀ (a b r : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
      0 ≤ r → r ≤ (V i).value (Set.Ico a b) →
      a ≤ cutAnswer V i a r ∧ cutAnswer V i a r ≤ b ∧
      (V i).value (Set.Ico a (cutAnswer V i a r)) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc a b →
        r ≤ (V i).value (Set.Ico a z) → cutAnswer V i a r ≤ z)
    (Q : Piece) (hQ : Q.WF) (s : Rec ι)
    (hs : s.Valid V N) (hQs : s.Aligned Q)
    (w : ℝ) (hw : 0 ≤ w) (p : Pos)
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
      s'.Aligned (prefixList Q p) ∧ s'.Aligned (suffixList Q p) := by sorry
