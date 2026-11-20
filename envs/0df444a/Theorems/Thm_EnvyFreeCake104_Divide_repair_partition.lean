-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_repair_partition
-- name    : EnvyFreeCake104.Divide.repair_partition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T17:23:14.426216+00:00
-- url     : https://prove2.me/theorems/c1d235a9-0fe1-493c-9612-324ff8670935
-- title:
--   Repair returns a partial allocation of the residue plus the old bundles
-- statement:
--   **Repair allocates part of $R\cup\bigcup_i D_i$ and returns the rest as residue.** Let $N$ be a set of agents, $\varepsilon\in\mathbb R$, $(D_i)_{i\in N}$ pairwise disjoint well-formed pieces and $R$ a well-formed piece disjoint from every $D_i$, all with endpoints recorded in a record state valid for $N$.
--
--   Then every successful run of $\mathrm{Repair}(N,D,R,\varepsilon)$ (Algorithm 4; any choice oracle, any prior transcript) returning bundles $(W_i)_{i\in N}$ and residue $U$ satisfies
--   $$W_i\cap W_j=\emptyset\ (i\ne j),\qquad W_i\subseteq R\cup\bigcup_{j\in N}D_j,\qquad U=\Big(R\cup\bigcup_{j\in N}D_j\Big)\setminus\bigcup_{i\in N}W_i .$$
--
--   This is Line 9 of Algorithm 4 ("return allocation $W$ and residue $(R\cup(\bigcup_i D_i))\setminus\bigcup_i W_i$"), stated for every run, without the value hypotheses of Lemma 4.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, arXiv:2610.30370v1, Algorithm 4 (p.11), Line 9

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Repair (Algorithm 4) returns a partial allocation of `R ∪ ⋃ D_i` with the residue of
Line 9: every successful run returns pairwise disjoint bundles inside `R ∪ ⋃ D_i`, and its
residue is `(R ∪ ⋃ D_i) \ ⋃ W_i`. -/
theorem repair_partition {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (D : ι → Piece) (R : Piece) (ε : ℝ) (hD : ∀ i ∈ N, (D i).WF) (hR : R.WF)
    (hDdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (D i).toSet (D j).toSet)
    (hDR : ∀ i ∈ N, Disjoint (D i).toSet R.toSet)
    (s : Rec ι) (hs : s.Valid V N) (hDs : ∀ i ∈ N, s.Aligned (D i)) (hRs : s.Aligned R)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (W : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((repair N D R ε).run s) tr₀ = some (((W, U), s'), tr)) :
    (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W i).toSet (W j).toSet) ∧
    (∀ i ∈ N, (W i).toSet ⊆ R.toSet ∪ ⋃ j ∈ N, (D j).toSet) ∧
    U.toSet = (R.toSet ∪ ⋃ j ∈ N, (D j).toSet) \ ⋃ i ∈ N, (W i).toSet := by sorry

end EnvyFreeCake104.Divide
