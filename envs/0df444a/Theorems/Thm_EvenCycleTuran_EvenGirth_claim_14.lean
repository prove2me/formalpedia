-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_claim_14
-- name    : EvenCycleTuran.EvenGirth.claim_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:45.213582+00:00
-- url     : https://prove2.me/theorems/bac34c9b-96bc-4c7d-95a7-18bfeb605a1d
-- title:
--   Claim 14, p. 21 — a path of length l−1 of multiplicity > 2k(k−l)/(l−2) yields, for every l ≤ r ≤ k, a C₂ᵣ containing a path of multiplicity ≥ 2k(k−r)/(l−2)
-- statement:
--   Let $k>l\ge3$ and let $G$ be a finite graph with no cycle of length $3,\dots,2l-1$. Run the greedy procedure of §5.2: go through the fat copies of $C_{2l}$ of $G$ in an arbitrary order, and from each pick one of its $2l$ paths of length $l-1$, always one that has been picked the smallest number of times so far; let $m(Q)$ be the number of times the path $Q$ of length $l-1$ was picked. Suppose some path $Q$ of length $l-1$ has
--   $$m(Q)>\frac{2k(k-l)}{l-2}.$$
--   Then for every $l\le r\le k$ there is a copy of $C_{2r}$ in $G$ that contains a path $Q_r$ of length $l-1$ with
--
--   $$m(Q_r)\ge\frac{2k(k-r)}{l-2}.$$
--
--   At $r=k$ this gives a $C_{2k}$ in $G$; this is how the proof of Theorem 14 bounds the multiplicities in a $C_{2k}$-free graph.
--
--   **Formalization Note.** The run is given by `cyc : Fin N → G.Subgraph`, a repetition-free list of all fat copies of $C_{2l}$, and `pick`, with `pick t` a path of length $l-1$ of `cyc t` picked before step $t$ at most as often as any other path of length $l-1$ of `cyc t` (`IsGreedyRun`). Paths are subgraphs isomorphic to `pathGraph l`, i.e. vertex lists up to reversal. The fractions are real numbers ($l\ge3$, so $l-2>0$). $G$ is not assumed $C_{2k}$-free: on the page $G$ is $C_{2k}$-free and the conclusion at $r=k$ is the contradiction, so assuming it here would make the hypotheses jointly unsatisfiable. The proof on the page uses only the girth bound, through Claims 12 and 13.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 21, Claim 14 (greedy procedure and multiplicity m(Q): p. 21, second and third paragraphs of §5.2)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem claim_14 {V : Type*} [Fintype V] (G : SimpleGraph V) (k l : ℕ) (hl : 3 ≤ l) (hkl : l < k)
    (hG : EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l - 1)) G)
    (N : ℕ) (cyc pick : Fin N → G.Subgraph) (hrun : IsGreedyRun G l N cyc pick)
    (Q : G.Subgraph) (hQ : Nonempty (pathGraph l ≃g Q.coe))
    (hmQ : 2 * (k : ℝ) * ((k : ℝ) - l) / ((l : ℝ) - 2) < (multiplicity pick Q : ℝ)) :
    ∀ r : ℕ, l ≤ r → r ≤ k → ∃ C : G.Subgraph, IsCycleCopy G (2 * r) C ∧
      ∃ Qr : G.Subgraph, IsSubpath l C Qr ∧
        2 * (k : ℝ) * ((k : ℝ) - r) / ((l : ℝ) - 2) ≤ (multiplicity pick Qr : ℝ) := by sorry

end EvenCycleTuran.EvenGirth
