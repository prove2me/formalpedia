-- Prove2me | Theorems.Thm_AbelianPromises_Dichotomy_Supplement_pruning_minion_equivalence
-- name    : AbelianPromises.Dichotomy.Supplement.pruning_minion_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:56:40.325524+00:00
-- url     : https://prove2.me/theorems/d9f4fda5-5c14-40ac-8450-e33f13195635
-- title:
--   Lemma C.12 — Singleton affine pruning and minion solutions
-- statement:
--   Let $L$ be any finite Label Cover instance and $N$ any abstract minion. Every vertex of $L$ has a nonempty finite domain, and every directed edge carries a total projection, from source to target. There exists an $N$-solution after constraint singleton AIP pruning exactly when the original instance has an $\omega_{\mathrm{CSinglAIP}}(N)$-solution:
--
--   $$
--   \kappa_{\mathrm{CSinglAIP}}(L)\to N
--   \quad\Longleftrightarrow\quad
--   L\to\omega_{\mathrm{CSinglAIP}}(N).
--   $$
--
--   Here an $N$-solution assigns a member at each vertex's domain arity and respects every edge minor. The construction $\kappa$ runs tuple pinning and signed-integer AIP pruning to a fixed point and then restricts domains, leaving isolated domains unchanged. Rejection has no solution. The minion $N$ need not be finite, functional, or given with an oracle. Neither a solution nor an AIP feasibility certificate is assumed.
--
--   This is the supporting equivalence used by the companion characterisation in Theorem C.15. It applies to parallel edges, disconnected instances, isolated vertices, and the empty vertex set.
--
--   Differences from the source:
--   - encoding: arbitrary nonempty finite coordinate and column sets → all nonempty finite subsets of Nat for coordinates and Fin(j+1) for arbitrary finite columns; reason: a size-unbounded finite-set skeleton; bijective reindexing preserves every instance and minor.
--   - encoding: minor operations and the omega construction → the exact graph of each derived minor operation; reason: the graph records the same fibre-sum matrix and restricted minor without assuming derived closure facts.
--   - encoding: pruning to a fixed point and restricting domains → simultaneous tuple deletion for N0+1 rounds followed by all incident positional compatibility tests; reason: finite monotone deletion gives the same greatest fixed point, and fixed-point pinned feasibility makes all incident supports agree; isolated domains are unchanged.
--   - encoding: empty initial domains or relations interpreted as unsatisfiable → kappa returns rejection for any empty current domain or relation, including an initially empty isolated domain; reason: makes the nonempty-domain LC construction total on empty templates without removing any satisfiable source instance.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, STOC 2027 submission #967 (October 2026). Canonical submission artifact; no arXiv pin or acceptance claim. printed p. 20 (PDF p. 21), Lemma C.12.

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Supplement_LabelCover
import Definitions.Def_AbelianPromises_Dichotomy_Supplement_SkeletalOmega

set_option autoImplicit false

namespace AbelianPromises.Dichotomy.Supplement

/-- Lemma C.12, with all finite Label Cover instances and arbitrary abstract minions. -/
theorem pruning_minion_equivalence (L : LabelCover) (N : AbstractMinion) :
    PrunedHasSolution L.toLCData N.presentation ↔
      L.toLCData.HasSolution (omega N.presentation) := by sorry

end AbelianPromises.Dichotomy.Supplement
