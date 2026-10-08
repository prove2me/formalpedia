-- Prove2me | Theorems.Thm_ConstrNestedLogit_Pricing_optimal_of_same_order
-- name    : ConstrNestedLogit.Pricing.optimal_of_same_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:02.027884+00:00
-- url     : https://prove2.me/theorems/ca57b499-70ec-484d-b04a-0afe624de339
-- title:
--   §6, p. 24 — the optimal solutions of (12) depend only on the ordering and signs of $\{f_{ij}(u) : j\in N_k\cup\{0\}\}$
-- statement:
--   Consider nest $i$ of the joint assortment and pricing problem, with $v_{i0}=0$ and positive preference weights $v_{ij}>0$. Let $u,u'\ge 0$, and write $f_{ij}(u)=v_{ij}(r_{ij}-u)$ together with $f_{i0}\equiv 0$. Suppose that for every product $k\in P$ the values $\{f_{ij}(u):j\in N_k\cup\{0\}\}$ and $\{f_{ij}(u'):j\in N_k\cup\{0\}\}$ are in the same weak order, that is, for all $j,j'\in N_k$,
--   $$
--   f_{ij}(u)\le f_{ij'}(u)\iff f_{ij}(u')\le f_{ij'}(u'),\qquad f_{ij}(u)\le 0\iff f_{ij}(u')\le 0,\qquad f_{ij}(u)\ge 0\iff f_{ij}(u')\ge 0 .
--   $$
--   Then for every assortment $S_i$: $S_i$ is an optimal solution of problem (7) over $\mathcal C_i$ at $u$ if and only if it is an optimal solution at $u'$.
--
--   This is the paper's key observation for joint assortment and pricing: as long as $u$ stays between two successive intersection points of the lines $\{f_{ij}:j\in N_k\cup\{0\}\}$, $k\in P$, the ordering and signs of the coefficients, hence the optimal solution, do not change.
--
--   **Formalization Note** "Same ordering and signs" is formalized as the same weak order on $N_k\cup\{0\}$ for every $k$, comparing only virtual products of the same product. The hypotheses $v_{ij}>0$ and $v_{i0}=0$ are added as in the rest of the mission.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 24, §6, the key observation on problem (12)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Pricing_Model

namespace ConstrNestedLogit.Pricing

open NestedLogitVariants.LP

/-- §6, p. 24: if at `u` and `u'` the values `{f_ij : j ∈ N_k ∪ {0}}` (with `f_i0 = 0`) are in the
same weak order for every product `k`, then an assortment is optimal for problem (7) at `u` if and
only if it is optimal at `u'`. -/
theorem optimal_of_same_order {ι : Type*} {n p : ℕ} (I : Instance ι n) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (prod : Fin n → Fin p) (u u' : ℝ) (hu : 0 ≤ u) (hu' : 0 ≤ u')
    (horder : ∀ j j', prod j = prod j' →
      (coeff I i u j ≤ coeff I i u j' ↔ coeff I i u' j ≤ coeff I i u' j'))
    (hsign_le : ∀ j, coeff I i u j ≤ 0 ↔ coeff I i u' j ≤ 0)
    (hsign_ge : ∀ j, 0 ≤ coeff I i u j ↔ 0 ≤ coeff I i u' j)
    (S : Finset (Fin n)) :
    IsOptimal7 I prod i u S ↔ IsOptimal7 I prod i u' S := by sorry

end ConstrNestedLogit.Pricing
