-- Prove2me | Theorems.Thm_CoDecompFO_Supplement_theorem_1_11
-- name    : CoDecompFO.Supplement.theorem_1_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:50:20.352979+00:00
-- url     : https://prove2.me/theorems/dd12c384-e466-4b96-841b-6764950071d4
-- title:
--   Theorem 1.11 — graphs of arbitrarily large twin-width with path co-width at most $3$
-- statement:
--   For every $d\in\mathbb N$ there is a finite simple graph $G$ whose twin-width is greater than $d$ and which is the limit of a path co-decomposition of graphs of width at most $3$:
--
--   $$\forall d\ \exists G:\quad \mathrm{tww}(G)>d\quad\text{and}\quad \mathrm{pcow}(G)\le 3 .$$
--
--   Since tree co-width is at most path co-width, bounded tree co-width does not imply bounded twin-width, although first-order model checking is tractable for both parameters.
--
--   **Formalization Note** Twin-width is the published partition form (`TwinWidthLE`); the graph has vertex set $\{0,\dots,n-1\}$ and the isomorphism with the limit is one of $\sigma_G$-structures.
--
--   Differences from the source:
--   - encoding: a graph of twin-width greater than d → a SimpleGraph on Fin n with ¬ TwinWidthI.BoolWidth.TwinWidthLE G d (published partition form); reason: twin-width is a parameter of finite simple graphs; a finite vertex set is Fin n up to relabelling
--   - encoding: path co-width at most 3 (the minimum width of a path co-decomposition with limit G) → some co-decomposition whose tree has maximum degree ≤ 2, of width ≤ 3, with lim T ≃[σ_G] G; reason: a minimum is ≤ 3 iff some decomposition has width ≤ 3; a tree of maximum degree ≤ 2 is a path
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Theorem 1.11 and its footnote a, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_CoDecompFO_Supplement_GraphSig
import Definitions.Def_TwinWidthI_BoolWidth_Setting

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

/-- **Theorem 1.11** (Bumpus, Gomes, Larios-Jones, Turner, *Co-Decompositions and FO Model Checking*,
arXiv:2611.04658, held file sha256 d550d7af…, p.3): "There are graphs of arbitrarily large twin-width whose path
co-width is at most 3." For every `d` there is a finite simple graph of twin-width greater than `d` that is the
limit of a path co-decomposition of graphs of width at most `3`.

**Formalization Note** Twin-width is the published partition form `TwinWidthI.BoolWidth.TwinWidthLE`, and
"twin-width greater than `d`" is `¬ TwinWidthLE G d`. The graph is on `Fin n`; a finite simple graph is a
symmetric loopless graph in the paper's sense (¶2.1, p.6), and the limit is isomorphic to it as a `σ_G`-structure
(`PathCoWidthLE`). The footnote's witness `K₃^d` and its cited twin-width `2d` ([70, Prop. 3.6]) are not part of
the statement. -/
theorem theorem_1_11 (d : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), ¬ TwinWidthI.BoolWidth.TwinWidthLE G d ∧ PathCoWidthLE G 3 := by sorry

end Supplement

end CoDecompFO
