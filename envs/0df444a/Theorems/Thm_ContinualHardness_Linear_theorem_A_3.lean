-- Prove2me | Theorems.Thm_ContinualHardness_Linear_theorem_A_3
-- name    : ContinualHardness.Linear.theorem_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:13:14.915851+00:00
-- url     : https://prove2.me/theorems/4d6693de-b599-45c2-8a65-1ebca9607e3a
-- title:
--   Theorem A.3 — Smooth-Label-Cover with smoothness, 4^R preimages, consistent label weighting and weak expansion is NP-hard to distinguish: satisfiable vs value below 2^(−c0 R)
-- statement:
--   There is a constant $c_0>0$ such that for all integers $Q,R\ge1$ it is NP-hard to distinguish, for Smooth-Label-Cover instances $L(G(V,E),N,M,\{\pi^{e,v}\})$ with $M=7^{(Q+1)R}$ and $N=2^R7^{QR}$,
--   * (**YES Case**) some labeling satisfies every edge, from
--   * (**NO Case**) every labeling satisfies less than a fraction $2^{-c_0R}$ of the edges,
--
--   where in both cases $L$ moreover has the properties of `Props Q R`: $G$ is a regular connected graph; (**Smoothness**) for every vertex $w$ and $i\ne j\in[M]$, $\Pr_{e\sim w}[\pi^{e,w}(i)=\pi^{e,w}(j)]\le1/Q$; every preimage $(\pi^{e,v})^{-1}(i)$ has at most $q=4^R$ elements; (**Consistent label weighting**) there are $\Lambda_v:[M]\to\{1,2,\dots,2^{(Q+1)R}\}$ with $\sum_{j\in(\pi^{e,v})^{-1}(i)}\Lambda_v(j)=\sum_{j\in(\pi^{e,w})^{-1}(i)}\Lambda_w(j)$ for every edge $e=(v,w)$ and $i\in[N]$; (**Weak Expansion**) every $V'\subseteq V$ with $|V'|=\delta|V|$ induces at least $\delta^2|E|$ edges. NP-hard means Karp gap hardness:
--   $$\mathrm{GapNPHard}\big(\mathrm{enc},\ \mathrm{Props}_{Q,R}\wedge\mathrm{Satisfiable},\ \mathrm{Props}_{Q,R}\wedge\mathrm{ValueBelow}(2^{-c_0R})\big):$$
--   every NP language over a finite nonempty alphabet maps in polynomial time to codes of instances, members to YES instances and non-members to NO instances. The source of the hardness of Theorem 3.1.
--
--   Differences from the source:
--   - reading: it is NP-hard to distinguish between the following two cases → SetCoverThreshold.SetCover.GapNPHard encodeSLC Yes No (Karp reduction from every NP language, members ↦ YES, non-members ↦ NO); reason: the standard meaning, and the one the composition with Theorem A.8 uses
--   - reading: In addition, the instance L satisfies the following properties → Props Q R is a conjunct of both the YES and the NO promise sets; reason: the properties are promised for the instances in both cases
--   - encoding: a regular connected (undirected) graph G(V, E); Pr_{e∼w} over a randomly chosen incident edge; |V′| = δ·|V| for any δ > 0 → an indexed family of edges with E ≥ 1 (loops and parallel edges allowed, counted with multiplicity, a loop at both ends), equal degrees, connected underlying simple graph; count of edge-ends at w ≤ degree/Q; every nonempty V′ with δ := |V′|/|V|; reason: Lean representation of Definition A.2; Appendix B's construction produces parallel edges and loops, weak expansion for |V′| = 1 is satisfiable only with loops (INSIGHTS I5), and fractions of edges presuppose E ≥ 1
--   - reading: a regular connected (undirected) graph G(V, E) in Definition A.2 → an edge may be a loop (ends e = (v, v)); a loop lies inside every V′ containing v and counts at both of its ends in the degree; reason: weak expansion as printed needs |E|/|V|² > 0 edges inside a single vertex, so it is unsatisfiable on a loopless graph; the construction of [15] (Appendix B) produces loops (u = v is allowed); INSIGHTS I5
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 17, Theorem A.3 (PDF p. 18); pp. 25-26, Appendix B (PDF pp. 26-27)

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_ContinualHardness_Linear_SmoothLabelCover

namespace ContinualHardness.Linear

/-- Theorem A.3 (hardness of Smooth-Label-Cover), p. 17. There is a constant `c₀ > 0` such that for
all integers `Q, R ≥ 1` it is NP-hard to distinguish Smooth-Label-Cover instances with
`M = 7^{(Q+1)R}` and `N = 2^R 7^{QR}` having a labeling that satisfies every edge (YES) from those
in which every labeling satisfies less than a fraction `2^{−c₀R}` of the edges (NO), even when the
instances satisfy smoothness (`1/Q`), preimages of size at most `4^R`, consistent label weighting
and weak expansion (`SLCInstance.Props Q R`). -/
theorem theorem_A_3 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ Q R : ℕ, 1 ≤ Q → 1 ≤ R →
      SetCoverThreshold.SetCover.GapNPHard encodeSLC
        (fun L => L.Props Q R ∧ L.Satisfiable)
        (fun L => L.Props Q R ∧ L.ValueBelow ((2 : ℝ) ^ (-(c₀ * (R : ℝ))))) := by sorry

end ContinualHardness.Linear
