-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_protocols_records_monotone
-- name    : EnvyFreeCake104.Divide.protocols_records_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T17:17:43.466291+00:00
-- url     : https://prove2.me/theorems/aec8f5c1-580f-46a8-a9a4-97fe75d0cdb2
-- title:
--   The protocols keep recorded values exact and only add recorded points
-- statement:
--   **Recorded values are maintained.** Fix a set $N$ of agents. A record state stores a finite set of points of $[0,1]$ (containing $0$ and $1$) and, for each agent, a value for each cell between consecutive points; it is *valid* for $N$ when every recorded cell value of every agent of $N$ equals her true value (§1.3).
--
--   For each of the protocols Permute (Algorithm 5), Core (Algorithm 3), Repair (Algorithm 4), the loop of Lines 9–11 of Dominate (Algorithm 2), and Dominate itself, every successful run (any inputs, any choice oracle, any prior transcript) from records $s$ to records $s'$ satisfies
--   $$s \text{ valid for } N \implies s' \text{ valid for } N, \qquad \mathrm{pts}(s)\subseteq \mathrm{pts}(s').$$
--
--   This is the bookkeeping of §1.3: the protocols only add Cut points, and whenever a new point splits a cell, one Eval query per participating agent records the value of one part and subtraction gives the other, so recorded values stay exact.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, arXiv:2610.30370v1, §1.3 (Recorded values, pp.4-5)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- §1.3 bookkeeping: every successful run of Permute, Core, Repair, the Shrink loop of
Dominate (Lines 9-11), and Dominate keeps valid records valid and only adds recorded points. -/
theorem protocols_records_monotone {ι : Type} [DecidableEq ι] (V : ι → Valuation)
    (N : Finset ι) :
    (∀ (P : ι → Piece) (s : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
        (x : (ι → Piece) × Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((permute N P).run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) ∧
    (∀ (c : ι) (C : Piece) (s : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
        (x : (ι → Piece) × Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((core N c C).run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) ∧
    (∀ (D : ι → Piece) (R : Piece) (ε : ℝ) (s : Rec ι) (o : ChoiceOracle ι)
        (tr₀ : List (Event ι)) (x : (ι → Piece) × Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((repair N D R ε).run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) ∧
    (∀ (istar : ι) (α : ℝ) (U : Piece) (fuel : ℕ) (W : ι → Piece) (R' : Piece) (s : Rec ι)
        (o : ChoiceOracle ι) (tr₀ : List (Event ι)) (x : (ι → Piece) × Piece) (s' : Rec ι)
        (tr : List (Event ι)),
        Prog.run V o ((shrink N istar α U fuel W R').run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) ∧
    (∀ (fuel : ℕ) (C : Piece) (s : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
        (x : (ι → Piece) × Piece × Finset ι) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((dominate fuel N C).run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) := by sorry

end EnvyFreeCake104.Divide
