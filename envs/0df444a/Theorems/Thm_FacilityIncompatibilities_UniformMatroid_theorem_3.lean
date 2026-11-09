-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_theorem_3
-- name    : FacilityIncompatibilities.UniformMatroid.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:33.305119+00:00
-- url     : https://prove2.me/theorems/c34641f8-2427-4537-86fb-8080fb472934
-- title:
--   Theorem 3 — a polynomial-time (1+√2+ε)-approximation for FL-MI with uniform opening costs
-- statement:
--   Fix any real $\varepsilon>0$. There is a single deterministic oracle Turing machine $T$ and a polynomial $p$ such that the following holds for every FL-MI instance with uniform opening costs: $n$ clients, $m$ facilities, a rational (pseudo)metric $d$ on the $n+m$ points, a rational common opening cost $f\ge0$, and any matroid $\mathcal M$ on the clients for which the whole facility set $V_F$ is feasible.
--
--   Run on the binary input word of $(n,m,d,f)$, of length $B$, with the independence oracle of $\mathcal M$, the machine $T$ halts within $p(B)$ steps, where every oracle answer counts as one step, and outputs a facility set $S\subseteq V_F$ together with a feasible assignment $\sigma:V_C\to S$ such that
--
--   $$\sum_{i\in S}f+\sum_{j\in V_C}d(j,\sigma(j))\ \le\ (1+\sqrt2+\varepsilon)\cdot\mathrm{OPT}.$$
--
--   Here $\mathrm{OPT}$ is the minimum of the objective over all feasible solutions. $T$ and $p$ depend only on $\varepsilon$, not on the instance or the matroid. Since the oracle answers in time polynomial in $|V_C|$, this is the source's polynomial-time $(1+\sqrt2+\varepsilon)$-approximation algorithm.
--
--   This is the first main result of the paper; for uniform matroids it is capacitated facility location with uniform capacities.
--
--   **Formalization Note** The machine model is the published `QAdvFew.PoQOracle.OTM` (work tape and query tape; the oracle reads the bit string on the query tape). The input and output codes and the oracle convention are those of the definition `Encoding`. The bound is on the number of machine steps, which also bounds the number of oracle queries.
--
--   Differences from the source:
--   - generalization: metric distances → a rational pseudometric table (distinct points may be at distance 0); reason: every metric instance is covered, so the machine must in particular handle the source's instances
--   - encoding: “a (1 + √2 + ε)-approximation algorithm” running in polynomial time with polynomially many independence-oracle calls → ∃ oracle Turing machine T and polynomial p (depending only on ε) such that for every valid encoded instance and matroid, T halts within p(|input|) steps (one step per oracle answer) with output encoding (S, σ), σ feasible, cost ≤ (1+√2+ε)·OPT; reason: polynomial time is invariant among standard machine models; the oracle's own polynomial running time composes with the step bound
--   - encoding: rational distances and opening costs, matroid given by an independence oracle → binary input word of n, m, the (n+m)² rational table and f; oracle on n-bit characteristic vectors (other queries answered false); output word = characteristic vector of S and binary indices σ(j); reason: explicit encoding conventions of the source's computational model; no instance is excluded
--   - encoding: uniform opening costs f_i = f ≥ 0 and V_F feasible → one rational f in the encoded instance; Valid (pseudometric, f ≥ 0, matroid ground = clients) and IsFeasible univ as hypotheses; reason: the same instances as the source
--   - encoding: OPT the optimum objective → OPT = min over facility sets of F(X) + A(X) in ℝ≥0∞, compared via ENNReal.ofReal; reason: OPT is finite because V_F is feasible; the same inequality
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Theorem 3, printed p.4 / PDF p.5; proof §3, printed p.13 / PDF p.14; computational conventions §1, printed p.2 / PDF p.3, and §1.2, printed pp.3–4 / PDF pp.4–5

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Encoding

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid

/-- **Theorem 3** (printed p.4 / PDF p.5): there exists a `(1 + √2 + ε)`-approximation algorithm
for FL-MI with uniform opening costs.

For every fixed `ε > 0` there are one deterministic oracle Turing machine `T` and one polynomial
`p` such that, for every rationally encoded instance with uniform opening cost (metric data,
`f ≥ 0`, `V_F` feasible) and every client matroid `M` on exactly the clients, the run of `T`
with the independence oracle of `M` on the encoded instance halts within `p(B)` steps
(`B` the input length; every oracle answer counts one step) and outputs the code of a facility
set `S` with a feasible assignment `σ : V_C → S` of total cost at most `(1 + √2 + ε) · OPT`. -/
theorem theorem_3 (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : QAdvFew.PoQOracle.OTM) (p : Polynomial ℕ),
      ∀ (E : EncodedInstance) (M : Matroid (Fin E.n)),
        (E.toInstance M).Valid → (E.toInstance M).IsFeasible Finset.univ →
        ∃ t : ℕ, t ≤ p.eval (encode E).length ∧
          T.result (indepOracle M) (encode E) t ≠ none ∧
          ∃ (S : Finset (Fin E.m)) (σ : Fin E.n → Fin E.m),
            T.output (indepOracle M) (encode E) t = encodeSolution S σ ∧
            (E.toInstance M).IsFeasibleAssignment S σ ∧
            ENNReal.ofReal ((E.toInstance M).solCost S σ) ≤
              ENNReal.ofReal (1 + Real.sqrt 2 + ε) * (E.toInstance M).OPT := by sorry

end FacilityIncompatibilities.UniformMatroid
