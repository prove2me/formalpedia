-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_dominate_invariants
-- name    : EnvyFreeCake104.Divide.dominate_invariants
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T17:02:15.116255+00:00
-- url     : https://prove2.me/theorems/94df7b63-f155-44f7-a4b9-dd0fe410a545
-- title:
--   Dominate keeps the records valid and returns a well-formed aligned residue
-- statement:
--   **Run invariant of Dominate.** Let $N$ be a set of $n\ge3$ agents, $C$ a well-formed piece (a finite list of pairwise disjoint intervals of $[0,1]$), and $s$ a record state that is valid for $N$ (§1.3: $0,1$ are recorded points and every recorded cell value of every agent of $N$ is her true value) and in which every endpoint of $C$ is a recorded point.
--
--   Then every successful run of $\mathrm{Dominate}(N,C)$ (Algorithm 2, any fuel, any choice oracle, any prior transcript) ends in records $s'$ that are again valid for $N$, and the residue $R$ it returns is a well-formed piece all of whose endpoints are recorded in $s'$.
--
--   This is the standing convention of §1.3 ("every piece our protocols handle is a union of intervals in the partition determined by 0, 1, and all previously returned Cut points ... subroutine and recursive calls inherit these records"), stated for the residue that Divide (Algorithm 1, Line 8) passes to its recursive call $\mathrm{Divide}(E,R)$.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, arXiv:2610.30370v1, §1.3 (Recorded values, p.4) and Algorithm 1 Line 8 / Algorithm 2 (pp.5-7)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Run invariant of Dominate (Algorithm 2) used by the recursion of Divide (p.5): from valid
records in which the cake is aligned, every successful run of `Dominate(N, C)` leaves valid
records, and the returned residue `R` is a well-formed piece aligned with the final records. -/
theorem dominate_invariants {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 3 ≤ N.card) (C : Piece) (hC : C.WF) (s : Rec ι) (hs : s.Valid V N)
    (hCs : s.Aligned C) (fuel : ℕ) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (X : ι → Piece) (R : Piece) (E : Finset ι) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((dominate fuel N C).run s) tr₀ = some (((X, R, E), s'), tr)) :
    s'.Valid V N ∧ R.WF ∧ s'.Aligned R := by sorry

end EnvyFreeCake104.Divide
