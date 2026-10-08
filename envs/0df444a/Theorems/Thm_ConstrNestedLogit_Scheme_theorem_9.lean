-- Prove2me | Theorems.Thm_ConstrNestedLogit_Scheme_theorem_9
-- name    : ConstrNestedLogit.Scheme.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:47.377236+00:00
-- url     : https://prove2.me/theorems/fda8adde-34f9-4c9e-b985-fd83430076fb
-- title:
--   Theorem 9 — for every α > 1, O(⌈α/(α−1)⌉ n^{⌈α/(α−1)⌉+2}) candidates include an α-approximate solution of (7)
-- statement:
--   Consider a nest $i$ of the nested logit model with preference weights $v_{ij}>0$, revenues $r_{ij}$ (of any sign), no within-nest no-purchase weight, and space constraints $\mathcal C_i=\{S:\sum_{j\in S}w_{ij}\le c_i\}$ with $0<w_{ij}\le c_i$ and $c_i\ge0$. Write $V_i(S)=\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$ (with $R_i(\emptyset)=0$). For every $\alpha>1$, with $q=\lceil\alpha/(\alpha-1)\rceil$, there is a collection $\{A_i^t:t\in\mathcal T_i\}\subseteq\mathcal C_i$ with
--
--   $$
--   |\mathcal T_i|\le 5\,(q+1)\,n^{q+2}+1
--   $$
--
--   such that for every $u\ge0$ some member $\hat S$ of the collection is an $\alpha$-approximate solution of problem (7):
--
--   $$
--   V_i(S)\big(R_i(S)-u\big)\le \alpha\,V_i(\hat S)\big(R_i(\hat S)-u\big)\qquad\text{for every } S\in\mathcal C_i .
--   $$
--
--   Combined with Theorem 4 and Theorem 2 of the paper, this yields an $\alpha$-approximation for the space-constrained assortment problem through a linear program with $1+m$ variables and $O(m\lceil\alpha/(\alpha-1)\rceil n^{\lceil\alpha/(\alpha-1)\rceil+2})$ constraints.
--
--   **Formalization Note** The paper's $O(\lceil\alpha/(\alpha-1)\rceil n^{\lceil\alpha/(\alpha-1)\rceil+2})$ is pinned to the explicit bound $5(q+1)n^{q+2}+1$, uniform in $q$ like the paper's: for $n\ge1$, at most $(q+1)n^q$ sets $J$ of size at most $q$, times at most $2n(n+1)+1\le5n^2$ pieces of $[0,\infty)$ (the open intervals between the at most $n(n+1)$ intersection points of the lines $h_{ij}$ and $f_{ij}$, and the points themselves); the $+1$ covers $n=0$. The collection is fixed before $u$. $v_{ij}>0$, $w_{ij}>0$ and $c_i\ge0$ are added; $w_{ij}\le c_i$ is the paper's assumption. Products are `Fin n`, nests a finite type, and the within-nest no-purchase weight of the published model is set to zero.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 40, Theorem 9

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Scheme_Model

namespace ConstrNestedLogit.Scheme

open NestedLogitVariants.LP in
/-- Theorem 9, p. 40: under space constraints, for every `α > 1`, with `q = ⌈α/(α − 1)⌉`, there is
a collection `A` of space-feasible assortments of nest `i` with at most
`5 (q + 1) n^(q + 2) + 1` members (the paper's `|T_i| = O(⌈α/(α − 1)⌉ n^{⌈α/(α−1)⌉+2})`)
that contains an `α`-approximate solution of problem (7) for every `u ≥ 0`. -/
theorem theorem_9 {ι : Type*} {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n) (hvnp : ∀ i, I.vnp i = 0)
    (hv : ∀ i j, 0 < I.v i j) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (hwc : ∀ i j, w i j ≤ c i) (hw : ∀ i j, 0 < w i j) (hc : ∀ i, 0 ≤ c i) (i : ι)
    (α : ℝ) (hα : 1 < α) :
    ∃ A : Finset (Finset (Fin n)), (∀ S ∈ A, ConstrNestedLogit.Space.spaceFeasible w c i S) ∧
      A.card ≤ 5 * (⌈α / (α - 1)⌉₊ + 1) * n ^ (⌈α / (α - 1)⌉₊ + 2) + 1 ∧
      ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A, ∀ S', ConstrNestedLogit.Space.spaceFeasible w c i S' →
        V I i S' * (R I i S' - u) ≤ α * (V I i S * (R I i S - u)) := by sorry

end ConstrNestedLogit.Scheme
