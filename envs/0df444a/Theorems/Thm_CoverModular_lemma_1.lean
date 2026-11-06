-- Prove2me | Theorems.Thm_CoverModular_lemma_1
-- name    : CoverModular.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:33.280765+00:00
-- url     : https://prove2.me/theorems/c2591860-5462-42d6-8578-641633196a6f
-- title:
--   Lemma 1 — weak-duality bound on $f(\mathcal S\cup\mathcal T)$ from a dual feasible solution for $\mathcal S$
-- statement:
--   Fix one scenario: capacities $c_i\ge0$, demands $d_j\ge0$ and profits $p_{ij}\ge0$, and let $f$ be the second-stage value (3). For any two sets of arcs $\mathcal S,\mathcal T\subseteq\mathcal F$ and any pair $(\alpha^{\mathcal S},\beta^{\mathcal S})$ feasible for the dual (4) with $\mathcal A=\mathcal S$,
--
--   $$
--   f(\mathcal S\cup\mathcal T)\le\sum_i c_i\alpha^{\mathcal S}_i+\sum_j d_j\beta^{\mathcal S}_j+\sum_{(i,j)\in\mathcal T\setminus\mathcal S}\min(c_i,d_j)\bigl(p_{ij}-\alpha^{\mathcal S}_i-\beta^{\mathcal S}_j\bigr)^+ .\tag{5}
--   $$
--
--   The first two sums are the dual objective of $(\alpha^{\mathcal S},\beta^{\mathcal S})$; the last sum is a dual estimate of the gains from the arcs of $\mathcal T$ not in $\mathcal S$. This lemma is the weak-duality step behind inequality (7) of Theorem 1.
--
--   **Formalization Note** §3.1 fixes a scenario and drops $\omega$; the statement is for one scenario's data.
--
--   Differences from the source:
--   - encoding: capacities c_i and demands d_j carry no printed sign → hypotheses c_i ≥ 0 and d_j ≥ 0; reason: they are capacities and demands; LP (3) is infeasible otherwise and display (6) splits only into > 0 and = 0, so only instances where f is undefined are excluded
--   - encoding: f(𝒜) = max of LP (3) → lpValue = sSup of the objective values over the feasible set; reason: the feasible set contains x = 0 and is bounded when c, d ≥ 0, so the supremum is attained and equals the maximum
--   - generalization: supply nodes 1..m and demand nodes 1..n → arbitrary finite types I, J (possibly empty); reason: the paper's index sets are an instance; with an empty index set every sum is empty and the statement stays true
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.1, Lemma 1, display (5), p.10

import Mathlib
import Definitions.Def_CoverModular_lpValue
import Definitions.Def_CoverModular_IsDualFeasible

namespace CoverModular

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- **Lemma 1** (DeValve, Pekeč, Wei, *Approximate submodularity in network design problems*,
SSRN 3844987, §3.1, Lemma 1, display (5), p.10). Fix one scenario (capacities `c`, demands
`d`, profits `p`). For any `𝒮, 𝒯 ⊆ 𝓕` and any dual feasible solution `(α^𝒮, β^𝒮)` of (4)
for `𝒜 = 𝒮`,
`f(𝒮 ∪ 𝒯) ≤ ∑_i c_i α^𝒮_i + ∑_j d_j β^𝒮_j + ∑_{(i,j) ∈ 𝒯 \ 𝒮} min(c_i, d_j)(p_ij − α^𝒮_i − β^𝒮_j)^+`.

**Formalization Note** §3.1 fixes one scenario `ω` and drops it; the statement is for one
scenario's data. `c, d ≥ 0` are the standing conditions (capacities and demands); `p ≥ 0` is
printed on p.6. -/
theorem lemma_1 (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (hp : ∀ i j, 0 ≤ p i j)
    (S T : Finset (I × J)) (α : I → ℝ) (β : J → ℝ) (hαβ : IsDualFeasible p S α β) :
    lpValue c d p (S ∪ T) ≤ ∑ i, c i * α i + ∑ j, d j * β j +
      ∑ a ∈ T \ S, min (c a.1) (d a.2) * max (p a.1 a.2 - α a.1 - β a.2) 0 := by sorry

end CoverModular
