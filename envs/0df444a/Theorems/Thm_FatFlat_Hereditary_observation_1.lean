-- Prove2me | Theorems.Thm_FatFlat_Hereditary_observation_1
-- name    : FatFlat.Hereditary.observation_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:33.225486+00:00
-- url     : https://prove2.me/theorems/37254f82-1146-46e4-a35f-8f9b6a7eb355
-- title:
--   Observation 1 — patterns contain bipartite patterns and vice versa (all five items)
-- statement:
--   Fix $r\ge3$ and $n,m\in\mathbb N$. Then each of the following holds (each "contains as an induced subgraph" is an injective map preserving and reflecting adjacency):
--   1. $K(r,n+m)$ contains $K(r,n,m)$ as an induced subgraph;
--   2. $W(r,n+m)$ contains $W(r,n,m)$ as an induced subgraph;
--   3. $K(r,n,\binom n2)$ contains $K(2r+1,n)$ as an induced subgraph;
--   4. $W(r,n,\binom n2)$ contains $W(2r,n)$ as an induced subgraph;
--   5. $M(r,\binom n2,n)$ contains $K(2r,n)$ as an induced subgraph.
--
--   Differences from the source: none.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Observation 1, p. 19 (PDF p. 21). Verbatim: 'Observation 1. Fix r ⩾ 3 and n, m ∈ N. Patterns contain bipartite patterns: 1. K(r, n+m) contains K(r, n, m) as an induced subgraph. 2. W(r, n+m) contains W(r, n, m) as an induced subgraph. Bipartite patterns contain patterns: 3. K(r, n, (n choose 2)) contains K(2r+1, n) as an induced subgraph. 4. W(r, n, (n choose 2)) contains W(2r, n) as an induced subgraph. 5. M(r, (n choose 2), n) contains K(2r, n) as an induced subgraph.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Observation 1** (arXiv:2607.21474, p. 19). Fix `r ≥ 3` and `n, m ∈ ℕ`.
1. `K(r, n+m)` contains `K(r, n, m)` as an induced subgraph.
2. `W(r, n+m)` contains `W(r, n, m)` as an induced subgraph.
3. `K(r, n, C(n,2))` contains `K(2r+1, n)` as an induced subgraph.
4. `W(r, n, C(n,2))` contains `W(2r, n)` as an induced subgraph.
5. `M(r, C(n,2), n)` contains `K(2r, n)` as an induced subgraph. -/
theorem observation_1 (r n m : ℕ) (hr : 3 ≤ r) :
    Nonempty (subdividedBiclique r n m ↪g subdividedClique r (n + m)) ∧
    Nonempty (biweb r n m ↪g web r (n + m)) ∧
    Nonempty (subdividedClique (2 * r + 1) n ↪g subdividedBiclique r n (n.choose 2)) ∧
    Nonempty (web (2 * r) n ↪g biweb r n (n.choose 2)) ∧
    Nonempty (subdividedClique (2 * r) n ↪g mixweb r (n.choose 2) n) := by sorry

end FatFlat.Hereditary
