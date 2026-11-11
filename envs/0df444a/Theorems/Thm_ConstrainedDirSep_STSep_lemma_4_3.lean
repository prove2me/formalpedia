-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_4_3
-- name    : ConstrainedDirSep.STSep.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:05:58.198253+00:00
-- url     : https://prove2.me/theorems/7a66264e-ba23-451a-9a16-b5b1d081007a
-- title:
--   Lemma 4.3 — every window is closed under coordinatewise minimum and maximum
-- statement:
--   Let $Q$ be a finite set of quadrant constraints on a pair of variables with domains $[d_i]$, $[d_j]$, thresholds in the ranges of (1)–(2), and window $W\subseteq[d_i]\times[d_j]$. Then for all $(p,q),(p',q')\in W$
--   $$(\min(p,p'),\min(q,q'))\in W\quad\text{and}\quad(\max(p,p'),\max(q,q'))\in W.$$
--
--   Min–max closure of windows is what lets Lemmas 4.6 and 4.7 solve each branch of the Chain CSP algorithm (Theorem 4.8).
--
--   Differences from the source:
--   - generalization: d_i, d_j ≥ 1 (domains of a Chain CSP) → any d_i, d_j ≥ 0; reason: an empty domain gives an empty window, and the source instance is the case d_i, d_j ≥ 1.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 16 (PDF 19), Lemma 4.3 (proof p. 41, PDF 44)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Quadrant

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 16 (PDF 19), Lemma 4.3: every window `W_ij` is closed under coordinatewise
minimum and maximum. -/
theorem lemma_4_3 (Q : Finset Quadrant) (di dj : ℕ)
    (hQ : ∀ c ∈ Q, c.WellRanged di dj) :
    MinMaxClosed (window Q di dj) := by sorry

end ConstrainedDirSep.STSep
