-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_round_weight_bound
-- name    : FlowOptimalSeparators.MinorFree.round_weight_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:08:08.299669+00:00
-- url     : https://prove2.me/theorems/2bb7cf46-a65e-4fdf-9c6a-3e42f4a62f88
-- title:
--   Lemma 4 — round vertex-weight norm
-- statement:
--   Let $h\ge3$, let $G$ be $K_h$-minor-free with $n$ vertices, and use Section 4's parameters $\mu=1$, $\iota=0$, and $D=\sqrt{n/T}$ with $T>0$. For every actual connector prefix of length less than $T$, let $w_t$ be the weight vector at its next attempted round. Then
--   $$\|w_t\|_1\le6n.$$
--   The prefix condition concerns only the preceding rounds, so the bound includes the attempted round that returns a separator. It is not asserted for arbitrary load vectors.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: exactly 3n/4 terminals; line 10 chooses them outside the root → ceil(3n/4) terminals, excluding the root whenever enough other cluster vertices exist; reason: the printed count is undefined off multiples of four; at n=401 a 301-vertex cluster needs the root to reach 301 terminals; this agrees with the source when four divides n
--   - encoding: the regularization n deg(v)/(2m) in an attempted FTRL round → 0 < m for the FTRL-round lemmas; reason: this excludes only division by zero in the source formula; zero-edge and empty inputs remain covered by the goal and need no FTRL rounds
--   - generalization: in every round → the next attempted round after any source-valid prefix of length less than T; reason: every actual prefix is included, and the proof uses only the preceding legal transitions; this includes the last attempted round without assuming a further connector
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 16–17, Lemma 4, Section 4 parameters

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_FTRLTrace

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Lemma 4, p.16 (proof p.17): the next attempted round after any actual prefix,
including an attempt that returns a separator. D is exactly Section 4's square root. -/
theorem round_weight_bound {n : ℕ} (G : Graph n) (h : ℕ) (hh : 3 ≤ h)
    (hG : ExcludesClique G h) (hm : 0 < edgeCount G) (T : ℕ) (hT : 0 < T)
    (Cs : List (WideConnector G)) (ht : Cs.length < T)
    (hrun : IsFTRLPrefix G (Real.sqrt ((n : ℝ) / T)) 1 0 Cs) :
    (∑ v, |roundWeight G (Real.sqrt ((n : ℝ) / T)) 1 0 Cs v|) ≤ 6 * n := by sorry

end FlowOptimalSeparators.MinorFree
