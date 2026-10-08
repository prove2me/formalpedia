-- Prove2me | Theorems.Thm_ConstrNestedLogit_Space_refined_chain
-- name    : ConstrNestedLogit.Space.refined_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:44.577212+00:00
-- url     : https://prove2.me/theorems/f8976841-ff66-410f-a59b-ade97fe1e82e
-- title:
--   Refined knapsack inequality for small products
-- statement:
--   Suppose every product in nest $i$ consumes at most a fraction $\epsilon\in[0,1)$ of the capacity: $w_{ij}\le\epsilon c_i$. If $x$ is an LP optimum for (10) with one fractional coordinate and $S^g=\{j:x_j=1\}$, then every feasible assortment $T$ satisfies
--
--   $$\sum_{j\in T}v_{ij}(r_{ij}-u)\le\frac{1}{1-\epsilon}\sum_{j\in S^g}v_{ij}(r_{ij}-u).$$
--
--   This is the first-to-last consequence of the inequality chain in §5.2, and identifies the rounded assortment as a $1/(1-\epsilon)$-approximate solution.
--
--   **Formalization Note** The statement omits the chain's intermediate quotients, which may divide by zero when the rounded assortment is empty.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 22, §5.2 displayed chain

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

namespace ConstrNestedLogit.Space

/-- The first and last terms of the §5.2 chain, without the paper's intermediate divisions. -/
theorem refined_chain {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ k, 0 < I.v i k)
    (hw : ∀ k, 0 < w i k) (hwc : ∀ k, w i k ≤ c i)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hsmall : ∀ k, w i k ≤ ε * c i)
    (u : ℝ) (hu : 0 ≤ u) (x : Fin n → ℝ)
    (hx : spaceLPOptimal I w c i u x) (j : Fin n)
    (hj : oneFractional x j) :
    ∀ T : Finset (Fin n), spaceFeasible w c i T →
      assortmentUtility I i u T ≤
        (1 / (1 - ε)) * assortmentUtility I i u (rounded x) := by sorry

end ConstrNestedLogit.Space
