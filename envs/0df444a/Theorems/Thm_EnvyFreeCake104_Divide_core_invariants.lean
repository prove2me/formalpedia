-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_core_invariants
-- name    : EnvyFreeCake104.Divide.core_invariants
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T17:21:09.971668+00:00
-- url     : https://prove2.me/theorems/1206eb28-d1c4-408f-b102-12398cd08f10
-- title:
--   Core keeps records valid and returns well-formed aligned pieces
-- statement:
--   **Core keeps pieces well formed.** Let $N$ be a set of $n\ge2$ agents, $c\in N$ a designated cutter, and $C$ a well-formed piece (a finite list of pairwise disjoint intervals of $[0,1]$) whose endpoints are recorded in a record state $s$ that is valid for $N$.
--
--   Then every successful run of $\mathrm{Core}(c,N,C)$ (Algorithm 3; any choice oracle, any prior transcript) ending in records $s'$ satisfies: $s'$ is valid for $N$, every point recorded in $s$ is recorded in $s'$, every returned bundle $Y_i$ ($i\in N$) is a well-formed piece with endpoints recorded in $s'$, and so is the returned residue $U$.
--
--   This is the §1.3 convention for the outputs of Core, used whenever Dominate passes Core's outputs to Repair or to a later Core call.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, arXiv:2610.30370v1, §1.3 (pp.4-5); Algorithm 3 (p.10)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Run invariant of Core (Algorithm 3): from valid records in which the well-formed cake is
aligned, every successful run keeps the records valid, only adds recorded points, and returns
well-formed aligned bundles and a well-formed aligned residue. -/
theorem core_invariants {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (c : ι) (hc : c ∈ N) (C : Piece) (hC : C.WF)
    (s : Rec ι) (hs : s.Valid V N) (hCs : s.Aligned C)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (Y : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((core N c C).run s) tr₀ = some (((Y, U), s'), tr)) :
    s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (Y i).WF ∧ s'.Aligned (Y i)) ∧
      U.WF ∧ s'.Aligned U := by sorry

end EnvyFreeCake104.Divide
