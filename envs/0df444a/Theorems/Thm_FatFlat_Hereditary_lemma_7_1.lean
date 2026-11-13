-- Prove2me | Theorems.Thm_FatFlat_Hereditary_lemma_7_1
-- name    : FatFlat.Hereditary.lemma_7_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:17.042852+00:00
-- url     : https://prove2.me/theorems/ea7fc75b-c39b-4f0f-b45c-ad2f617d8d49
-- title:
--   Lemma 7.1 — a hereditary FSMF class excludes large $K(r,k)$ and $W(r,k)$
-- statement:
--   Let $\mathcal C$ be a hereditary graph class that is fat-shallow-minor-free. Then for every $r\ge3$ there is $k\in\mathbb N$ such that no graph of $\mathcal C$ contains $K(r,k)$ or $W(r,k)$ as an induced subgraph.
--
--   Differences from the source:
--   - reading: C excludes K(r, k) and W(r, k) → no G ∈ C has an induced-subgraph embedding of K(r, k) or of W(r, k) (PatternFree C); reason: 'excludes' as in Theorem 1.2 (4), which this lemma proves; for a hereditary class it is the same as K(r, k), W(r, k) ∉ C
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Lemma 7.1, p. 21 (PDF p. 23). Verbatim: 'Lemma 7.1. For every hereditary FSMF graph class C and every r ⩾ 3, there is k ∈ N such that C excludes K(r, k) and W(r, k).' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Lemma 7.1** (arXiv:2607.21474, p. 21). For every hereditary FSMF graph class `C` and every
`r ≥ 3` there is `k ∈ ℕ` such that `C` excludes `K(r, k)` and `W(r, k)` (as induced
subgraphs). -/
theorem lemma_7_1 (C : GraphClass) (hC : IsHereditary C) (hF : FSMF C) : PatternFree C := by sorry

end FatFlat.Hereditary
