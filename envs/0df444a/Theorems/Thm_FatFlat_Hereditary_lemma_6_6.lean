-- Prove2me | Theorems.Thm_FatFlat_Hereditary_lemma_6_6
-- name    : FatFlat.Hereditary.lemma_6_6
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:24.156469+00:00
-- url     : https://prove2.me/theorems/0dd813cf-86ff-4310-811c-2ec731be0145
-- title:
--   Lemma 6.6 — a $d$-shallow induced $K(3,M,M)$ yields an induced $K(r,m,m)$, $W(r,m,m)$ or $M(r,m,m)$ with $3\le r\le 8d+3$
-- statement:
--   For all $d,m\in\mathbb N$ there is $M\in\mathbb N$ such that: if a finite graph $G$ contains $K(3,M,M)$ as a $d$-shallow induced minor, then there is $r$ with $3\le r\le 8d+3$ such that $G$ contains $K(r,m,m)$, $W(r,m,m)$ or $M(r,m,m)$ as an induced subgraph.
--
--   Differences from the source: none.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Lemma 6.6, p. 19 (PDF p. 21). Verbatim: 'Lemma 6.6. For every d, m ∈ N, there is M ∈ N with the following property. If a graph G contains K(3, M, M) as an d-shallow induced minor, then there is 3 ⩽ r ⩽ 8d+3 such that G contains K(r, m, m), W(r, m, m), or M(r, m, m) as an induced subgraph.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Lemma 6.6** (arXiv:2607.21474, p. 19). For every `d, m ∈ ℕ` there is `M ∈ ℕ` such that if a
graph `G` contains `K(3, M, M)` as a `d`-shallow induced minor, then there is
`3 ≤ r ≤ 8d + 3` such that `G` contains `K(r, m, m)`, `W(r, m, m)` or `M(r, m, m)` as an
induced subgraph. -/
theorem lemma_6_6 (d m : ℕ) : ∃ M : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    IsShallowInducedMinor (subdividedBiclique 3 M M) G d →
    ∃ r : ℕ, 3 ≤ r ∧ r ≤ 8 * d + 3 ∧
      (Nonempty (subdividedBiclique r m m ↪g G) ∨ Nonempty (biweb r m m ↪g G) ∨
        Nonempty (mixweb r m m ↪g G)) := by sorry

end FatFlat.Hereditary
