-- Prove2me | Theorems.Thm_DDNNFNeg_proposition_5_1_obdd
-- name    : DDNNFNeg.proposition_5_1_obdd
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:38.777757+00:00
-- url     : https://prove2.me/theorems/68aacfd7-1d92-4a21-af4d-0b4a186eff17
-- title:
--   Proof of Proposition 5.1 (corrected: $n \ge 1$) — “$G_x$ has colour $c$ but not $c'$” has an OBDD of size $\le 8n$
-- statement:
--   Let $G$ be a 3-regular graph on $[n]$, $n \ge 1$, with a proper 3-edge-colouring, and let $c \ne c'$ be two colours. Then there is an OBDD $B$ — a branching program with no $\vee$ vertices, at most one sink of each label, reading the variables in one fixed order on every path — that computes
--   $$
--   x \mapsto \big[\, G_x \text{ contains colour } c \text{ but not colour } c' \,\big]
--   $$
--   and has at most $8n$ vertices.
--
--   The construction reads the cycles of the 2-regular graph formed by the edges of colours $c$ and $c'$ one at a time, remembering three bits.
--
--   **Formalization Note** The size counts every vertex, sinks included. The hypothesis $n \ge 1$ excludes the empty graph, which is vacuously 3-regular and for which no branching program has at most $8 \cdot 0 = 0$ vertices.
--
--   Differences from the source:
--   - correction: a 3-regular graph G on [n] (any n) → additionally 0 < n; reason: at n = 0 the empty graph is vacuously 3-regular and every branching program has at least one vertex, so size ≤ 8n = 0 fails
--   - encoding: OBDD → BDD with no ∨ vertices, read-once, ordered by an injective π : Fin n → ℕ, with at most one sink of each label; reason: Definition 3.2's OBDD; read-once is implied by the ordering and stated for readability
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), proof of Proposition 5.1, p.12

import Mathlib
import Definitions.Def_DDNNFNeg_HasColor
import Definitions.Def_DDNNFNeg_IsProperEdgeColoring
import Definitions.Def_DDNNFNeg_BDD_Computes
import Definitions.Def_DDNNFNeg_BDD_IsReadOnce
import Definitions.Def_DDNNFNeg_BDD_IsDeterministic
import Definitions.Def_DDNNFNeg_BDD_IsOrderedBy
import Definitions.Def_DDNNFNeg_BDD_HasUniqueSinks

namespace DDNNFNeg

/-- **Proof of Proposition 5.1**, the OBDD construction (corrected: `n ≥ 1`) (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.12): for a
3-regular graph `G` on `[n]` with a proper 3-edge-colouring and two distinct colours
`col ≠ col'`, the condition "`G_x` contains colour `col` but not `col'`" is computed by an
OBDD with at most `8n` vertices.

**Formalization Note** The OBDD is a `BDD` with no `∨` vertices, read-once, ordered by an
injective `π : Fin n → ℕ`, with at most one sink of each label; its size counts every vertex,
sinks included. The hypothesis `0 < n` is a correction: on the empty graph (`n = 0`, vacuously
3-regular) every branching program has at least one vertex, so `size ≤ 8n = 0` fails. -/
theorem proposition_5_1_obdd {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (c : Sym2 (Fin n) → Fin 3) (hc : IsProperEdgeColoring G c)
    (col col' : Fin 3) (hne : col ≠ col') :
    ∃ B : BDD (Fin n), B.IsDeterministic ∧ B.IsReadOnce ∧
      (∃ π : Fin n → ℕ, Function.Injective π ∧ B.IsOrderedBy π) ∧ B.HasUniqueSinks ∧
      B.Computes (fun x => decide (HasColor G c x col ∧ ¬ HasColor G c x col')) ∧
      B.size ≤ 8 * n := by sorry

end DDNNFNeg
