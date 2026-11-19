-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_prefixPosition_first_crossing__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- name    : EnvyFreeCake104.Divide.prefixPosition_first_crossing__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T19:01:36.631409+00:00
-- url     : https://prove2.me/theorems/48d250a1-98ba-4f69-b3ca-e5987441b51d
-- title:
--   The pure interval-and-cell search returns the first value crossing
-- statement:
--   Assuming recorded-piece correctness and the local least-cut contract, the pure selector succeeds and returns the lexicographically earliest prefix crossing for any well-formed aligned piece and admissible request.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem EnvyFreeCake104.Divide.prefixPosition_first_crossing__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
    {ι : Type} (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (hs : s.Valid V N) (i : ι) (hi : i ∈ N)
    (hrecord : ∀ P : Piece, P.WF → s.Aligned P →
      s.pieceVal i P = (V i).value P.toSet)
    (hcut : ∀ (a b r : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
      0 ≤ r → r ≤ (V i).value (Set.Ico a b) →
      a ≤ cutAnswer V i a r ∧ cutAnswer V i a r ≤ b ∧
      (V i).value (Set.Ico a (cutAnswer V i a r)) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc a b →
        r ≤ (V i).value (Set.Ico a z) → cutAnswer V i a r ≤ z)
    (Q : Piece) (hQ : Q.WF) (hQs : s.Aligned Q)
    (w : ℝ) (hw : 0 ≤ w) (hwQ : w ≤ (V i).value Q.toSet) :
    ∃ p : Pos,
      (match findInterval s i Q 0 w with
        | none => if w ≤ 0 then some (Q.length, (0 : ℝ)) else none
        | some (k, r) =>
          if r ≤ 0 then some (k, (Q.getD k default).a)
          else
            match findCell s i
                ((s.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
                  c < (Q.getD k default).b)).sort (· ≤ ·)) r with
            | none => none
            | some (c, t) => some (k, cutAnswer V i c t)) = some p ∧
      (Q = [] ∨ Q.ValidPos p) ∧
      (V i).value (prefixList Q p).toSet = w ∧
      ∀ q : Pos, Q.ValidPos q →
        w ≤ (V i).value (prefixList Q q).toSet →
        p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2) := by sorry
