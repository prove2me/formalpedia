-- Prove2me | Theorems.Thm_EuclidCVRP_Main_claim_8
-- name    : EuclidCVRP.Main.claim_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:00.110542+00:00
-- url     : https://prove2.me/theorems/3a4ae932-db0d-4c3f-ac5f-992bcf8557f7
-- title:
--   Claim 8 — two curves covering a cycle of tours
-- statement:
--   Work in the setting of Section 2 (a valid $D$-bounded instance, an optimum $\mathrm{OPT}$ with at most $\Gamma$ nonempty tours, cells of side $\tau=\varepsilon^2/D$). Let $\mathrm{Cell}(T)$ be an admissible dense cell for every $T\in\mathrm{OPT}$ with $d(V_{\mathrm{left}}(T))>0$, and let $G$ be the digraph on $\mathrm{OPT}$ with an arc $(T,T')$, $T\ne T'$, whenever $T$ traverses $\mathrm{Cell}(T')$. For a directed cycle $T_1\to T_2\to\dots\to T_m\to T_1$ of $G$ ($m\ge2$) there are two closed polygonal curves $R_K$ and $B_K$ such that
--
--   1. both pass through the depot and traverse $\mathrm{Cell}(T_i)$ for every $i\in[m]$;
--   2. their lengths satisfy
--   $$c(R_K)+c(B_K)\le\sum_{i=1}^m c(T_i)+2\sqrt2\,m\tau;$$
--   3. $R_K\cup B_K$ covers the curves of $T_1,\dots,T_m$.
--
--   This is the cycle case in the proof of Lemma 7.
--
--   Differences from the source:
--   - reading: c(R_K) + c(B_K) ≤ ∑ c(T_i) + O(mτ) → the constant 2√2 mτ; reason: the constant the proof establishes (p. 10)
--   - reading: closed geometric curves → closed polygonal walks (lists of points); reason: R_K and B_K are built from polygonal subpaths of the tours and straight segments
--   - encoding: Section 2: a D-bounded instance and an optimum OPT with |OPT| ≤ Γ → Sec2.Setting: valid D-bounded instance, OPT optimal, at most Γ tours, all nonempty; D ≥ 1; reason: the tours of |OPT| are nonempty (a tour without clients is not counted); D ≥ 1 is implied by D-boundedness when n ≥ 1
--   - reading: a sufficiently fine square grid of cells of side τ = ε²/D partitioning the annulus; "the exact construction of the cells is not important" (p. 7) → the grid of half-open squares [a, a+τ) × [b, b+τ) with the depot at a grid vertex; K = (2⌈D/τ⌉+1)² cells cover the disc of radius D; reason: half-open cells partition the plane, so every client lies in exactly one cell; K depends only on ε and D
--   - generalization: "Fix one such cell and denote it by Cell(T)" (p. 8) → every choice of an admissible dense cell Cell(T) for each tour with d(V_left(T)) > 0; reason: holding for every choice specializes to the fixed one
--   - encoding: a cycle T_1, …, T_m in G → an injective map from Fin m (m ≥ 2) to the tours of OPT, each with d(V_left) > 0, with T_i traversing Cell(T_{i+1}) cyclically; reason: the definition of G: arcs need T ≠ T′ and end at tours whose Cell is defined
--   - encoding: visit the depot → the depot is a vertex of the walk; reason: the depot lies on the curve exactly when a walk can be taken through it as a vertex
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 9, Claim 8 (explicit constant 2√2 mτ from its proof, p. 10)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Section2

set_option autoImplicit false

namespace EuclidCVRP.Main

open Sec2

/-- **Claim 8** (p. 9; constant from its proof, p. 10). In the setting of Section 2, let `Cell(T)` be
an admissible dense cell of every tour `T ∈ OPT` with `d(V_left(T)) > 0`, and let `T₁ → ⋯ → T_m → T₁`
be a directed cycle of the auxiliary digraph `G` (an arc `(T, T')`, `T ≠ T'`, when `T` traverses
`Cell(T')`). Then there are two closed curves `R_K`, `B_K` through the depot, both traversing every
`Cell(Tᵢ)`, with `c(R_K) + c(B_K) ≤ ∑ c(Tᵢ) + 2√2 m τ` and whose union covers the curves of
`T₁, …, T_m`. -/
theorem claim_8 (ε : ℝ) (hε : 0 < ε) (D : ℝ) (hD : 1 ≤ D) (Γ : ℕ) (I : Instance)
    (OPT : List (List (Fin I.n))) (hset : Setting I D OPT Γ)
    (cell : Fin OPT.length → ℤ × ℤ)
    (hcell : ∀ j, 0 < I.demSet (Vleft I ε D OPT j) → IsDenseCell I ε D OPT j (cell j))
    (m : ℕ) (hm : 2 ≤ m) (cyc : Fin m → Fin OPT.length) (hinj : Function.Injective cyc)
    (hleft : ∀ i, 0 < I.demSet (Vleft I ε D OPT (cyc i)))
    (harc : ∀ i : Fin m, TraversedBy I ε D OPT (cyc i) (cell (cyc (finRotate m i)))) :
    ∃ R B : List Pt, I.depot ∈ R ∧ I.depot ∈ B ∧
      (∀ i, Traverses R (cellSet I ε D (cell (cyc i))) ∧
        Traverses B (cellSet I ε D (cell (cyc i)))) ∧
      closedLen R + closedLen B ≤
        ∑ i, I.tourCost OPT[cyc i] + 2 * Real.sqrt 2 * (m : ℝ) * τ ε D ∧
      ∀ i, curve (I.tourPts OPT[cyc i]) ⊆ curve R ∪ curve B := by sorry

end EuclidCVRP.Main
