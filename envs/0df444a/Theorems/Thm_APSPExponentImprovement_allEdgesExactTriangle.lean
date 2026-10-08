-- Prove2me | Theorems.Thm_APSPExponentImprovement_allEdgesExactTriangle
-- name    : APSPExponentImprovement.allEdgesExactTriangle
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T13:36:21.009988+00:00
-- url     : https://prove2.me/theorems/09914343-ce65-43e8-82b4-a37003ac6b49
-- title:
--   All-edges Exact Triangle in $O(n^r)$ for every $r>2.99825$
-- statement:
--   For every rational $r>2.99825$, solve all-edges Exact Triangle in $O(n^r)$ steps. Input consists of the AB, BC, and AC integer weight matrices of a complete tripartite graph with n vertices in each part. Output three row-major blocks of exactly zero/one flags, in AB, BC, AC order, indicating for every edge whether it belongs to a triangle whose three weights sum to zero. The accepting verdict is required even if every flag is zero. For every fixed natural weight exponent $\kappa$, there must be a single finite deterministic word-RAM program, a word-width constant $b$, and a time bound $T$ working for all sizes $n$ and all word widths $W\ge b(\operatorname{Nat.log2}(n)+1)$. Every encoded input integer has absolute value at most $n^\kappa$. Correctness includes $n=0,1$; the asymptotic bound is required for $n\ge2$. The machine must accept and write the required exact output. The program and constants may depend on r as well as the weight exponent. The strict exponent inequality leaves room to absorb fixed logarithmic factors.
-- source:
--   https://arxiv.org/html/2610.06783v1#S6; Theorems 17 and 19, conclusion footnote 10; https://people.csail.mit.edu/rrw/finding-full.pdf; https://theory.stanford.edu/~virgi/tria-mmult-jv.pdf

import Definitions.Def_APSPExponentImprovement_AllEdgesExactTriangle

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem APSPExponentImprovement.allEdgesExactTriangle :
    ∀ r : Rat, 2.99825 < r →
      APSPExponentImprovement.AllEdgesExactTriangle.SolvedInTime r := by sorry
