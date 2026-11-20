-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_permute_invariants
-- name    : EnvyFreeCake104.Divide.permute_invariants
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T17:17:44.611183+00:00
-- url     : https://prove2.me/theorems/b68f4114-0eaa-47eb-8f85-72d85ee34f4c
-- title:
--   Permute keeps records valid and returns well-formed aligned pieces
-- statement:
--   **Permute keeps pieces well formed.** Let $N$ be a set of agents and $(P_i)_{i\in N}$ pairwise disjoint pieces, each a finite list of pairwise disjoint intervals of $[0,1]$, all of whose endpoints are recorded in a record state $s$ valid for $N$.
--
--   Then every successful run of $\mathrm{Permute}(N,(P_i)_{i\in N})$ (Algorithm 5; any choice oracle, any prior transcript) ending in records $s'$ satisfies: $s'$ is valid for $N$; every point recorded in $s$ is recorded in $s'$; every returned bundle $Y_i$ ($i\in N$) is a well-formed piece whose endpoints are recorded in $s'$; and the returned residue $U$ (the list of all trimmed prefixes) is a well-formed piece whose endpoints are recorded in $s'$.
--
--   This is the §1.3 convention ("every piece our protocols handle is a union of intervals in the partition determined by 0, 1, and all previously returned Cut points") for the outputs of Permute.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, arXiv:2610.30370v1, §1.3 (Recorded values, pp.4-5); Algorithm 5 (p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Run invariant of Permute (Algorithm 5): from valid records in which the pairwise disjoint,
well-formed input pieces are aligned, every successful run keeps the records valid, only adds
recorded points, and returns well-formed aligned bundles and a well-formed aligned residue. -/
theorem permute_invariants {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (Y : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((permute N P).run s) tr₀ = some (((Y, U), s'), tr)) :
    s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (Y i).WF ∧ s'.Aligned (Y i)) ∧
      U.WF ∧ s'.Aligned U := by sorry

end EnvyFreeCake104.Divide
