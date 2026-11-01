-- Prove2me | Theorems.Thm_AndOrSched_section_2_normalization
-- name    : AndOrSched.section_2_normalization
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:28.2042+00:00
-- url     : https://prove2.me/theorems/106a5001-a6a9-48aa-954f-c9e1c4f2ec0f
-- title:
--   §2, p.6 — the w.l.o.g. normalization
-- statement:
--   Let $I$ be an instance with acyclic AND-precedences, let $I'$ be its normalized instance (zero-time jobs $Z$ removed, redundant OR-arcs removed, $A$-weights shifted to zero-time dummy successors in $B$, processing times scaled by $D$), and let $\Delta$ be the parameter of the paper. Then:
--   1. $I'$ has acyclic AND-precedences, $w_a=0$ on $A'$, integer processing times, $p_j\ge1$ for every job without predecessors, and no redundant OR-arcs;
--   2. $\Delta(I')\le\Delta(I)$ and $I'$ has at most $2|N|$ jobs;
--   3. if every $p_j\in\{0,1\}$ in $I$, then every processing time of $I'$ is in $\{0,1\}$;
--   4. for every feasible schedule $C$ of $I$ there is a feasible schedule $C'$ of $I'$ with $\sum_jw'_jC'_j\le D\sum_jw_jC_j$;
--   5. for every order $\prec$ of the jobs of $I'$ whose schedule $C'$ is feasible for $I'$, the schedule returned for $I$ (jobs of $Z$ at time $0$, the others at $C'_j/D$) is feasible for $I$ and costs at most $\frac1D\sum_jw'_jC'_j$.
--
--   Together these say that an approximation guarantee proved on normalized instances transfers, with the same ratio, to arbitrary instances.
--
--   Differences from the source:
--   - encoding: a precedence digraph E∧ → hypothesis `Acyclic I`; reason: a precedence graph is acyclic; the paper's transitive-closure and redundancy assumptions presuppose it
--   - reading: "pj ≥ 1 for every job … that has no predecessors (otherwise such a job can be disregarded)" → the least closed set Z of zero-time jobs is scheduled at time 0, and OR-successors of Z lose their OR-constraint; reason: deleting a zero-time OR-predecessor literally can raise the optimum (A = {a, a′}, p_a = 0, p_a′ = 1, P(b) = {a, a′}: optimum 1 before, 2 after)
--   - reading: "all data is integer" → rational processing times scaled by the lcm D of their denominators; weights stay real; reason: the analysis uses integrality of the processing times only; real processing times are not an algorithmic input
--   - reading: the w.l.o.g. remark → five explicit clauses (properties of I′, Δ′ ≤ Δ, size, {0,1} preserved, cost transfer both ways); reason: the remark has no formal statement; these are exactly the facts Theorem 1 needs
--   - encoding: a dummy successor for a job of A with positive weight → a dummy for every remaining a ∈ A; reason: a dummy of weight 0 changes no cost
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.6, "W.l.o.g., we may assume that wa = 0 for all a ∈ A. … (otherwise such a job can be disregarded)."

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_scaleD
import Definitions.Def_AndOrSched_normalize
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_outSched
open scoped Classical NNReal

namespace AndOrSched

/-- §2, p.6 (Happach, Schulz, arXiv:2001.07011v1): "W.l.o.g., we may assume that wa = 0 for all a ∈ A. Otherwise, we can shift a
positive weight of a job in A to an additional successor in B with zero processing time. Further,
we may assume that all data is integer and pj ≥ 1 for every job j ∈ N that has no predecessors
(otherwise such a job can be disregarded)."

For an instance `I` with acyclic AND-precedences, the normalized instance `I' = normalize I`
1. has acyclic AND-precedences and satisfies the w.l.o.g. assumptions (`IsNormalized`);
2. has `Δ(I') ≤ Δ(I)` and at most `2|N|` jobs;
3. has processing times in `{0, 1}` if `I` has;
4. has, for every feasible schedule `C` of `I`, a feasible schedule of cost at most `D · cost(C)`,
   `D = scaleD I`;
5. turns every order `σ` of its jobs whose schedule is feasible for `I'` into a feasible schedule of
   `I` (`outSched`) of cost at most `cost_{I'}(σ) / D`. -/
theorem section_2_normalization (I : Instance) (hI : Acyclic I) :
    Acyclic (normalize I) ∧ IsNormalized (normalize I) ∧ delta (normalize I) ≤ delta I ∧
    Fintype.card (normalize I).N ≤ 2 * Fintype.card I.N ∧
    ((∀ j, I.p j = 0 ∨ I.p j = 1) → ∀ j, (normalize I).p j = 0 ∨ (normalize I).p j = 1) ∧
    (∀ C : I.N → ℝ, IsFeasible I C →
      ∃ C' : (normalize I).N → ℝ, IsFeasible (normalize I) C' ∧
        cost (normalize I) C' ≤ (scaleD I : ℝ) * cost I C) ∧
    ∀ σ : (normalize I).N ≃ Fin (Fintype.card (normalize I).N),
      IsFeasible (normalize I) (listC (normalize I) σ) →
        IsFeasible I (outSched I σ) ∧
        cost I (outSched I σ) ≤ cost (normalize I) (listC (normalize I) σ) / (scaleD I : ℝ) := by sorry

end AndOrSched
