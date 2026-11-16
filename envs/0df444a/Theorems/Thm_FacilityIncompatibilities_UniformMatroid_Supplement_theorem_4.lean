-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_Supplement_theorem_4
-- name    : FacilityIncompatibilities.UniformMatroid.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:13:50.638234+00:00
-- url     : https://prove2.me/theorems/2e7b52ec-0c37-463d-9af7-4d8e3282737f
-- title:
--   Theorem 4 — a (15 + ε)-approximation for FL-MI with group constraints and non-uniform opening costs
-- statement:
--   Fix $\varepsilon>0$. There are a deterministic oracle Turing machine $T$ and a polynomial $p$ such that the following holds for every FL-MI instance $(V_C,V_F,d,f,\mathcal M)$ with $n$ clients and $m$ facilities, given by rational distances $d$ forming a (pseudo)metric and rational opening costs $f_i\ge0$ (arbitrary, not necessarily equal), whose client matroid $\mathcal M$ (ground set $V_C$) is a **partition matroid**, and in which $V_F$ is feasible. Run on the input word of length $B$ with the independence oracle of $\mathcal M$, the machine $T$ halts within $p(B)$ steps and outputs a facility set $S\subseteq V_F$ together with a feasible assignment $\sigma:V_C\to S$ (every $\sigma^{-1}(i)$ independent in $\mathcal M$) with
--
--   $$\sum_{i\in S}f_i+\sum_{j\in V_C}d(j,\sigma(j))\ \le\ (15+\varepsilon)\cdot\mathrm{OPT}.$$
--
--   Here $\mathrm{OPT}$ is the minimum cost of a feasible solution of the instance. The machine and the polynomial depend on $\varepsilon$ only, not on the instance, the matroid or its groups; the algorithm sees the matroid only through the oracle.
--
--   This is the paper's companion result for non-uniform opening costs; the mission's goal, Theorem 3, treats a general matroid with uniform opening costs.
--
--   **Formalization Note** The input word encodes $n$, $m$, the distance table and the $m$ opening costs; the output word is the characteristic vector of $S$ followed by the code of every $\sigma(j)$. Each oracle answer counts as one step. $\mathrm{OPT}$ is in `ℝ≥0∞`. The hypothesis that $V_F$ is feasible is the paper's standing assumption (printed p.2).
--
--   Differences from the source:
--   - generalization: metric distances d (Definition 1) → a pseudometric (distinct points may be at distance 0); reason: every metric satisfies these axioms, so every instance of the source is covered
--   - encoding: "there exists a (15 + ε)-approximation algorithm" with polynomially many oracle calls and polynomial running time in |V_C|, |V_F| and the bit length of the data (printed p.2) → one oracle Turing machine T and one polynomial p, chosen after ε, with T halting within p(input length) steps on every instance and outputting an encoded feasible solution of cost ≤ (15 + ε)·OPT; reason: the input length is at least |V_C| + |V_F| and at most polynomial in them and the bit length, so the two time bounds are equivalent
--   - encoding: groups G_g with bounds b_g ≥ 0 (Definition 2) → a label map grp : Fin n → Fin n and bounds b : Fin n → ℕ; reason: a partition of n clients has at most n nonempty parts and a cardinality bound is equivalent to its integer part
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Theorem 4, printed p.4 / PDF p.5 (proof §4, printed pp.14–20 / PDF pp.15–21); Definition 2 and oracle conventions printed p.2 / PDF p.3

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Supplement_NonUniform

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid.Supplement

/-- **Theorem 4** (printed p.4 / PDF p.5): there exists a `(15 + ε)`-approximation algorithm for
FL-MI with group constraints and non-uniform facility-opening costs.

For every fixed `ε > 0` there are one deterministic oracle Turing machine `T` and one polynomial
`p` such that, for every rationally encoded instance with per-facility opening costs (metric
data, `f ≥ 0`, `V_F` feasible) and every client matroid `M` on exactly the clients that is a
partition matroid, the run of `T` with the independence oracle of `M` on the encoded instance
halts within `p(B)` steps (`B` the input length; every oracle answer counts one step) and outputs
the code of a facility set `S` with a feasible assignment `σ : V_C → S` of total cost at most
`(15 + ε) · OPT`. -/
theorem theorem_4 (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : QAdvFew.PoQOracle.OTM) (p : Polynomial ℕ),
      ∀ (E : NUEncodedInstance) (M : Matroid (Fin E.n)),
        (E.toInstance M).Valid → IsPartitionMatroid M →
        (E.toInstance M).IsFeasible Finset.univ →
        ∃ t : ℕ, t ≤ p.eval E.encode.length ∧
          T.result (indepOracle M) E.encode t ≠ none ∧
          ∃ (S : Finset (Fin E.m)) (σ : Fin E.n → Fin E.m),
            T.output (indepOracle M) E.encode t = encodeSolution S σ ∧
            (E.toInstance M).IsFeasibleAssignment S σ ∧
            ENNReal.ofReal ((E.toInstance M).solCost S σ) ≤
              ENNReal.ofReal (15 + ε) * (E.toInstance M).OPT := by sorry

end FacilityIncompatibilities.UniformMatroid.Supplement
