-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_Supplement_theorem_19
-- name    : FacilityIncompatibilities.UniformMatroid.Supplement.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:14:43.382014+00:00
-- url     : https://prove2.me/theorems/b82aee7c-85ce-4824-a4ea-9ff790b20ee1
-- title:
--   Theorem 19 — no polynomial-time n^{1−ε}-approximation with overlapping group constraints unless P = NP
-- statement:
--   Fix $\varepsilon>0$. Consider facility location with **unrestricted overlapping group constraints**: $n$ clients, $m$ facilities, rational distances forming a (pseudo)metric, rational opening costs $f_i\ge0$, and groups $G_1,\dots,G_K$ of clients with bounds $b_k\in\mathbb N$, possibly overlapping and not necessarily covering the clients; an assignment $\sigma:V_C\to S$ is feasible if no facility of $S$ serves more than $b_k$ clients of any $G_k$.
--
--   Suppose there are a polynomial-time computable map $\mathcal A$ on bit strings and a threshold $N$ such that, for every such instance with $n\ge N$ clients in which $V_F$ is feasible, $\mathcal A$ maps the input word to (the code of) a facility set $S$ and a feasible assignment $\sigma:V_C\to S$ with
--
--   $$\sum_{i\in S}f_i+\sum_{j}d(j,\sigma(j))\ \le\ n^{1-\varepsilon}\cdot\mathrm{OPT}.$$
--
--   Then $\mathbf P=\mathbf{NP}$.
--
--   This shows that the partition assumption of Definition 2 cannot be dropped: with overlapping groups the problem is as hard to approximate as graph coloring. For $\varepsilon\ge1$ the ratio is below $1$ for $n\ge2$, so no such algorithm exists and the statement holds trivially, as in the source.
--
--   **Formalization Note** $\mathbf P$, $\mathbf{NP}$ and polynomial-time computability are those of the published `CookPvsNP_defs`; "unless $\mathbf P=\mathbf{NP}$" is an implication whose hypothesis is the existence of the algorithm. Nothing about the inapproximability of chromatic number is assumed. $n^{1-\varepsilon}$ is the real power, $\mathrm{OPT}$ is in `ℝ≥0∞`.
--
--   Differences from the source:
--   - generalization: a polynomial-time n^{1−ε}-approximation on every instance → the ratio is required only on instances with at least N clients, N chosen together with the algorithm; reason: an algorithm in the source's sense satisfies the hypothesis with N = 0, so the Lean statement implies the source's
--   - generalization: metric distances → a pseudometric (distinct points may be at distance 0); reason: every metric satisfies these axioms, and the paper's own reduction co-locates all points
--   - encoding: "admits no polynomial-time n^{1−ε}-approximation unless P = NP" → (∃ polynomial-time computable Alg : List Bool → List Bool with the ratio, outputting an encoded feasible solution) → P = NP, with Cook's P and NP; reason: the standard reading of "unless P = NP"
--   - encoding: groups and bounds b_k → a list of pairs (G_k ⊆ Fin n, b_k ∈ ℕ) written in the input word; V_F feasible as a hypothesis; reason: a cardinality bound is equivalent to its integer part; instances without any feasible solution have no approximate solution to output (standing assumption, printed p.2)
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Theorem 19, Appendix B.1, printed p.23 / PDF p.24 (proof printed pp.23–24 / PDF pp.24–25)

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Supplement_Hardness

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid.Supplement

/-- **Theorem 19** (printed p.23 / PDF p.24): for every fixed `ε > 0`, facility location with
unrestricted overlapping group constraints admits no polynomial-time `n^{1−ε}`-approximation
unless `P = NP`, where `n` is the number of clients.

Stated as: if some polynomial-time computable map `Alg` on bit strings and some threshold `N`
are such that, on every encoded instance with at least `N` clients (metric data, `f ≥ 0`,
arbitrary possibly overlapping groups, `V_F` feasible), `Alg` outputs the code of a feasible
solution `(S, σ)` of cost at most `n^{1−ε} · OPT`, then `P = NP`. -/
theorem theorem_19 (ε : ℝ) (hε : 0 < ε) :
    (∃ (Alg : List Bool → List Bool) (N : ℕ), CookPvsNP.PolyTimeComputable Alg ∧
      ∀ E : GroupEncodedInstance, N ≤ E.n → E.toGen.Valid →
        E.toGen.IsFeasible Finset.univ →
        ∃ (S : Finset (Fin E.m)) (σ : Fin E.n → Fin E.m),
          Alg E.encode = encodeSolution S σ ∧ E.toGen.IsFeasibleAssignment S σ ∧
          ENNReal.ofReal (E.toGen.solCost S σ) ≤
            ENNReal.ofReal ((E.n : ℝ) ^ (1 - ε)) * E.toGen.OPT) →
    PEqNP := by sorry

end FacilityIncompatibilities.UniformMatroid.Supplement
