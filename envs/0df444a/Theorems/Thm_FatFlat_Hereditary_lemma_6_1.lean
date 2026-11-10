-- Prove2me | Theorems.Thm_FatFlat_Hereditary_lemma_6_1
-- name    : FatFlat.Hereditary.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:24.482075+00:00
-- url     : https://prove2.me/theorems/890f0c8f-9688-4317-b37d-6ac70bc9217e
-- title:
--   Lemma 6.1 — a pattern-free graph class is ISMF
-- statement:
--   Let $\mathcal C$ be a graph class such that for every $r\ge3$ there is $k\in\mathbb N$ such that no graph of $\mathcal C$ contains $K(r,k)$ or $W(r,k)$ as an induced subgraph. Then $\mathcal C$ is induced-shallow-minor-free. No hereditary assumption is made.
--
--   Differences from the source: none.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Lemma 6.1, p. 17 (PDF p. 19). Verbatim: 'Lemma 6.1. Let C be a graph class such that for every r ⩾ 3, there is k ∈ N such that C excludes K(r, k) and W(r, k) as induced subgraphs. Then C is ISMF.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Lemma 6.1** (arXiv:2607.21474, p. 17). Let `C` be a graph class such that for every
`r ≥ 3` there is `k ∈ ℕ` such that `C` excludes `K(r, k)` and `W(r, k)` as induced subgraphs.
Then `C` is ISMF. -/
theorem lemma_6_1 (C : GraphClass) (hC : PatternFree C) : ISMF C := by sorry

end FatFlat.Hereditary
