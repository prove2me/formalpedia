-- Prove2me | Theorems.Thm_APSPExponentImprovement_apsp
-- name    : APSPExponentImprovement.apsp
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T14:44:33.837672+00:00
-- url     : https://prove2.me/theorems/9c4150fb-2e87-4412-bdd9-52c25d6283eb
-- title:
--   APSP in $O(n^{2.9983})$ word-RAM steps
-- statement:
--   Compute all exact shortest-path distances in a directed n-vertex graph with integer weights and no negative-weight closed walk in $O(n^{2.9983})$ deterministic word-RAM steps, where $2.9983=29983/10000$ exactly. Negative edges and missing edges are permitted. For each ordered vertex pair, output a reachability flag followed by a distance: flag one requires an attained minimum path weight, and flag zero requires that no path exists, with the distance slot then unrestricted. Empty paths give diagonal distance zero. For every fixed natural weight exponent $\kappa$, there must be a single finite deterministic word-RAM program, a word-width constant $b$, and a time bound $T$ working for all sizes $n$ and all word widths $W\ge b(\operatorname{Nat.log2}(n)+1)$. Every encoded input integer has absolute value at most $n^\kappa$. Correctness includes $n=0,1$; the asymptotic bound is required for $n\ge2$. The machine must accept and write the required exact output. There are no hypotheses assuming the supporting algorithms or any complexity conjecture.
-- source:
--   https://arxiv.org/html/2610.06783v1#S6; Theorems 17 and 19, conclusion footnote 10; https://people.csail.mit.edu/rrw/finding-full.pdf; https://theory.stanford.edu/~virgi/tria-mmult-jv.pdf

import Definitions.Def_TrulySubcubicAPSP_Problems

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem APSPExponentImprovement.apsp :
    TrulySubcubicAPSP.APSP.SolvedInTime 2.9983 := by sorry
