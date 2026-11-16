-- Prove2me | Theorems.Thm_CoDecompFO_Supplement_theorem_1_14
-- name    : CoDecompFO.Supplement.theorem_1_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:51:03.275479+00:00
-- url     : https://prove2.me/theorems/86a643b7-3f93-4744-9955-c4e232ed66d8
-- title:
--   Theorem 1.14 — $(s,t)$-PATH is NP-hard on co-decomposition inputs
-- statement:
--   The following problem is NP-hard: given a tree co-decomposition $\mathcal T$ of graphs and two matching families $s,t$ (but not $\lim\mathcal T$), decide whether $\lim\mathcal T$ has a directed path from $s$ to $t$. That is, every language $L\in\mathrm{NP}$, over any finite nonempty alphabet, has a polynomial-time many-one reduction to $\mathrm{PathCD}$:
--
--   $$L\le_p \mathrm{PathCD}\qquad\text{for every } L\in\mathrm{NP}.$$
--
--   Reachability is polynomial when the graph is given explicitly; the theorem shows that the succinct co-decomposition input makes it intractable unless $\mathrm P=\mathrm{NP}$, and $(s,t)$-PATH is not first-order expressible, so it is not covered by Theorem 1.16.
--
--   **Formalization Note** NP and reductions are those of the published `CookPvsNP_defs` (Cook's one-tape Turing machines).
--
--   Differences from the source:
--   - reading: NP-hard (no machine model named) → every L ∈ CookPvsNP.NP Sym, Sym finite and nonempty, satisfies CookPvsNP.PolyReducible L PathCD; reason: the standard Karp reading, over the published Turing-machine classes
--   - encoding: input: a tree co-decomposition and two matching families → pathCode T s t over Fin 3: the published encCoDecomp followed by the coordinates of s and t, in binary with separator 2; reason: the paper fixes no code; the code is injective and polynomial in the size of T
--   - reading: a path from s to t in lim T → Relation.ReflTransGen IsEdge s t: a directed path of length ≥ 0 along edges of lim T; reason: graphs are directed (¶2.1); an edge of the limit is an edge in every bag (¶2.7)
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Theorem 1.14, p.3 (PDF p.5); §3, ¶3.1–3.6, pp.8–10 (PDF pp.10–12)

import Mathlib
import Definitions.Def_CoDecompFO_Supplement_PathCD

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

/-- **Theorem 1.14** (Bumpus, Gomes, Larios-Jones, Turner, *Co-Decompositions and FO Model Checking*,
arXiv:2611.04658, held file sha256 d550d7af…, p.3; proof in §3, pp.8–10): "Given only a tree co-decomposition and
two matching families, (s,t)-PATH is NP-hard." Every language in NP, over any finite nonempty alphabet, reduces in
polynomial time to `PathCD`.

**Formalization Note** NP, polynomial-time computable functions and many-one reductions are those of the
published `CookPvsNP_defs` (one-tape Turing machines, Cook's Definitions 3–4); NP-hardness is the second half of
its `NPComplete`. The paper names no model; this is the standard Karp reading. The instance is coded over
`{0, 1, 2}` without the limit (`pathCode`). -/
theorem theorem_1_14 (Sym : Type) [Fintype Sym] [Nonempty Sym] (L : CookPvsNP.Lang Sym)
    (hL : L ∈ CookPvsNP.NP Sym) : CookPvsNP.PolyReducible L PathCD := by sorry

end Supplement

end CoDecompFO
