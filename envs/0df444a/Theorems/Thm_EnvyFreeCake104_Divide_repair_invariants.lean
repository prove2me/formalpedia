-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_repair_invariants
-- name    : EnvyFreeCake104.Divide.repair_invariants
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T17:21:08.851543+00:00
-- url     : https://prove2.me/theorems/97d2667d-6076-450f-841b-d5ed7c27a087
-- title:
--   Repair keeps records valid and returns well-formed aligned pieces
-- statement:
--   **Repair keeps pieces well formed.** Let $N$ be a set of agents, $\varepsilon\in\mathbb R$, $(D_i)_{i\in N}$ pairwise disjoint well-formed pieces (old bundles) and $R$ a well-formed piece (the residue) disjoint from every $D_i$, all with endpoints recorded in a record state $s$ valid for $N$.
--
--   Then every successful run of $\mathrm{Repair}(N,D,R,\varepsilon)$ (Algorithm 4; any choice oracle, any prior transcript) ending in records $s'$ satisfies: $s'$ is valid for $N$, every point recorded in $s$ is recorded in $s'$, every returned bundle $W_i$ ($i\in N$) is a well-formed piece with endpoints recorded in $s'$, and so is the returned residue (the unpicked cells followed by Permute's residue).
--
--   This is the §1.3 convention for the outputs of Repair: the cells are cut out of $R$ at recorded marks, the pieces passed to Permute are concatenations of disjoint cells and old bundles, and Permute only trims recorded prefixes.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, arXiv:2610.30370v1, §1.3 (pp.4-5); Algorithm 4 (p.11)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Run invariant of Repair (Algorithm 4): from valid records in which the pairwise disjoint
well-formed old bundles `D_i` and the well-formed residue `R` (disjoint from every `D_i`) are
aligned, every successful run keeps the records valid, only adds recorded points, and returns
well-formed aligned bundles and a well-formed aligned residue. -/
theorem repair_invariants {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (D : ι → Piece) (R : Piece) (ε : ℝ) (hD : ∀ i ∈ N, (D i).WF) (hR : R.WF)
    (hDdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (D i).toSet (D j).toSet)
    (hDR : ∀ i ∈ N, Disjoint (D i).toSet R.toSet)
    (s : Rec ι) (hs : s.Valid V N) (hDs : ∀ i ∈ N, s.Aligned (D i)) (hRs : s.Aligned R)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (W : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((repair N D R ε).run s) tr₀ = some (((W, U), s'), tr)) :
    s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (W i).WF ∧ s'.Aligned (W i)) ∧
      U.WF ∧ s'.Aligned U := by sorry

end EnvyFreeCake104.Divide
