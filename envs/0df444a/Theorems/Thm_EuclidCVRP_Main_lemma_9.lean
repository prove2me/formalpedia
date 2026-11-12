-- Prove2me | Theorems.Thm_EuclidCVRP_Main_lemma_9
-- name    : EuclidCVRP.Main.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:24.670577+00:00
-- url     : https://prove2.me/theorems/6581bc84-6d60-4e26-aa2b-92f194ae6004
-- title:
--   Lemma 9 — a walk P absorbing slack demand
-- statement:
--   Work in the setting of Section 2, with $\delta=\varepsilon/D$ and $\eta_{\mathrm{slack}}=\min\{\varepsilon/D,1/K\}$. There is an absolute constant $C>0$ (and an absolute $\varepsilon_0>0$) such that for every $\varepsilon\in(0,\varepsilon_0)$ there are a closed walk $P$ through the depot serving clients $V(P)$, and a solution $\mathrm{OPT}'$ of closed walks with $|\mathrm{OPT}'|=|\mathrm{OPT}|$ on the clients $V\setminus V(P)$ (each walk through the depot, each such client served exactly once, each walk of demand at most $Q$), such that
--
--   1. for every tour $T\in\mathrm{OPT}$: $V(P)\cap V(T)\subseteq V_{\mathrm{left}}(T)$, $d(V(P)\cap V(T))\le\eta_{\mathrm{slack}}Q_T+\delta Q$, and $d(V(T)\setminus V(P))\le Q-\eta_{\mathrm{slack}}Q_T$;
--   2. for every tour $T\in\mathrm{OPT}$ there is a walk $T'\in\mathrm{OPT}'$ with $V(T')=V(T)\setminus V(P)$;
--   3. the total length satisfies
--   $$c(P)+c(\mathrm{OPT}')\le\Bigl(\tfrac32+C\varepsilon\Bigr)\,c(\mathrm{OPT}).$$
--
--   Lemma 6 follows by partitioning $P$ into tours (Lemma 5).
--
--   Differences from the source:
--   - reading: O(ε), with ε > 0 ("throughout, we may assume that ε > 0 is sufficiently small, in particular ε < 1/2", p. 6) → an absolute constant C > 0 quantified before ε, D, Γ and the instance, and the claim for all ε ∈ (0, ε₀) for an absolute ε₀ > 0; reason: the paper's standing convention on ε; C never depends on D, since Theorem 1 takes D = D_ε
--   - encoding: Section 2: a D-bounded instance and an optimum OPT with |OPT| ≤ Γ → Sec2.Setting: valid D-bounded instance, OPT optimal, at most Γ tours, all nonempty; D ≥ 1; reason: the tours of |OPT| are nonempty (a tour without clients is not counted); D ≥ 1 is implied by D-boundedness when n ≥ 1
--   - reading: a sufficiently fine square grid of cells of side τ = ε²/D partitioning the annulus; "the exact construction of the cells is not important" (p. 7) → the grid of half-open squares [a, a+τ) × [b, b+τ) with the depot at a grid vertex; K = (2⌈D/τ⌉+1)² cells cover the disc of radius D; reason: half-open cells partition the plane, so every client lies in exactly one cell; K depends only on ε and D
--   - reading: a closed walk P and a solution OPT′ on clients V \ V(P) (closed walks, p. 11) → walks: lists of points through the depot with a served set of clients located at their vertices; OPT′ serves every client outside V(P) exactly once, none of V(P), each walk of demand ≤ Q; reason: OPT′ consists of closed walks with added boundary and parity segments (p. 11), not tours; the capacity condition is part of being a solution
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 10, Lemma 9

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Section2

set_option autoImplicit false

namespace EuclidCVRP.Main

open Sec2

/-- **Lemma 9** (p. 10). In the setting of Section 2 there are a closed walk `P` through the depot and a
solution `OPT'` by closed walks, with `|OPT'| = |OPT|`, on the clients `V \ V(P)`, such that
(i) for every `T ∈ OPT`, `V(P) ∩ V(T) ⊆ V_left(T)`, `d(V(P) ∩ V(T)) ≤ η_slack Q_T + δQ` and
`d(V(T) \ V(P)) ≤ Q − η_slack Q_T`; (ii) for every `T ∈ OPT` some `T' ∈ OPT'` has
`V(T') = V(T) \ V(P)`; (iii) `c(P) + c(OPT') ≤ (1.5 + O(ε)) c(OPT)`, the `O(ε)` an absolute constant. -/
theorem lemma_9 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ D : ℝ, 1 ≤ D → ∀ (Γ : ℕ) (I : Instance)
        (OPT : List (List (Fin I.n))), Setting I D OPT Γ →
        ∃ (P : Walk I) (W : List (Walk I)),
          P.Valid ∧ W.length = OPT.length ∧ (∀ w ∈ W, w.Valid) ∧
          (∀ w ∈ W, Disjoint w.serves P.serves) ∧
          (∀ v, v ∉ P.serves → W.countP (fun w => v ∈ w.serves) = 1) ∧
          (∀ w ∈ W, I.demSet w.serves ≤ I.Q) ∧
          (∀ j : Fin OPT.length,
            P.serves ∩ (OPT[j]).toFinset ⊆ Vleft I ε D OPT j ∧
            (I.demSet (P.serves ∩ (OPT[j]).toFinset) : ℝ) ≤
              ηslack ε D * QT I ε D OPT j + δ ε D * I.Q ∧
            (I.demSet ((OPT[j]).toFinset \ P.serves) : ℝ) ≤ I.Q - ηslack ε D * QT I ε D OPT j) ∧
          (∀ j : Fin OPT.length, ∃ w ∈ W, w.serves = (OPT[j]).toFinset \ P.serves) ∧
          P.cost + (W.map Walk.cost).sum ≤ (3 / 2 + C * ε) * I.cost OPT := by sorry

end EuclidCVRP.Main
