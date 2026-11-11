-- Prove2me | Theorems.Thm_FlowLatRound_fundamental_cycle_basis
-- name    : FlowLatRound.fundamental_cycle_basis
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:09.264075+00:00
-- url     : https://prove2.me/theorems/f1d2407f-9671-411b-9254-219da48a864f
-- title:
--   §3.1 — the signed fundamental cycles of a spanning tree form a basis of $\Lambda_G$
-- statement:
--   Let $G$ be a multigraph and $T$ a spanning tree, with cycle rank $d=m-n+1$. The fundamental-cycle matrix $C_T$ (column $j$ belongs to the $j$-th non-tree edge $e$ in increasing order) has entry $1$ at $e$ and vanishes on the other non-tree edges, and its $d$ columns form a $\mathbb Z$-basis of the flow lattice $\Lambda_G$.
--
--   Together with membership in $\Lambda_G$, the first condition identifies each column as the signed indicator vector of $C(T,e)$ with entry $+1$ at $e$. This is the basis output by the sampler of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
--   - encoding: H_G = ker A_G with one vertex row of the incidence matrix deleted → kernel of the full n×m incidence map; reason: the rows of the full matrix sum to zero, so both kernels are equal
--   - encoding: the signed indicator vectors of the fundamental cycles C(T, e) → the columns of fundMatrix G T (computed by tree search), with the conditions entry 1 at e and 0 on the other non-tree edges stated; reason: an integral flow supported on T ∪ {e} with value 1 at e is exactly the signed indicator of C(T, e)
--   - encoding: G connected, T a spanning tree → T a spanning tree of G; reason: a spanning tree exists iff G is connected
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), §3.1, p.6 (PDF 8); Appendix C opening, p.22 (PDF 24)

import Mathlib
import Definitions.Def_FlowLatRound_FundCycles

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), §3.1, p.6 (PDF 8), and Appendix C opening, p.22 (PDF 24): the signed indicator vectors
of the `d` fundamental cycles `C(T, e)`, `e ∉ T`, form a basis of `Λ_G`. For every multigraph `G`
and spanning tree `T`, the matrix `C_T = fundMatrix G T` (column `j` for the `j`-th non-tree edge
`e` in increasing order) has entry `1` at `e`, vanishes on the other non-tree edges, and its
`d = m − n + 1` columns form a `ℤ`-basis of `Λ_G`.

**Formalization Note.** The column conditions together with membership in `Λ_G` (part of the
basis property) determine each column as the signed indicator vector of `C(T, e)` with `+1` at
`e`. -/
theorem fundamental_cycle_basis {n m : ℕ} (G : MGraph n m) (T : Finset (Fin m))
    (hT : G.IsSpanningTree T) :
    (∀ (j : Fin (m + 1 - n)) (e : Fin m),
      ((List.finRange m).filter (fun f => f ∉ T))[j.1]? = some e →
        G.fundMatrix T e j = 1 ∧ ∀ f, f ∉ T → f ≠ e → G.fundMatrix T f j = 0) ∧
    IsZBasis G.flowLattice (G.fundMatrix T) := by sorry

end FlowLatRound
