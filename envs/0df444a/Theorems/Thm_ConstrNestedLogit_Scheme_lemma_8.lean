-- Prove2me | Theorems.Thm_ConstrNestedLogit_Scheme_lemma_8
-- name    : ConstrNestedLogit.Scheme.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:35.160218+00:00
-- url     : https://prove2.me/theorems/dc361dd8-0d01-4c32-b108-484e1391e862
-- title:
--   Lemma 8 — partially fixed relaxations give a q/(q−1)-approximate solution of (10)
-- statement:
--   Fix a nest $i$ with space requirements $w_{ij}>0$ and capacity $c_i\ge0$, and an integer $q\ge2$. For every $u\ge0$ there is a set $J\subseteq N$ with $|J|\le q$ (so $J\in\wp_q$) such that problem (17) at $(u,J)$ has an optimal solution with at most one fractional component and, for every such optimal solution $x$, the rounded-down assortment $S=\lfloor x\rfloor$ satisfies $S\in\mathcal C_i$ and
--
--   $$
--   \sum_{j\in S'}v_{ij}(r_{ij}-u)\le\frac{q}{q-1}\sum_{j\in S}v_{ij}(r_{ij}-u)\qquad\text{for every } S'\in\mathcal C_i .
--   $$
--
--   The paper states Lemma 8 for its collection $\{S_i^g(J):J\in\wp_q,\ g\in\mathcal G_i\}$, built from the optimal solutions $x_i^g(J)$ of (17) on the intervals $\mathcal I_i^g$; the statement above is the per-$u$ content of the lemma, and the counting of intervals is part of Theorem 9.
--
--   **Formalization Note** $q\ge2$ is added (at $q=1$ the factor $q/(q-1)$ is $1/0$, and the paper's $q=\lceil\alpha/(\alpha-1)\rceil$ is always at least 2). $w_{ij}>0$ and $c_i\ge0$ are added; the latter guarantees that the empty assortment is feasible.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 40, Lemma 8 (proof pp. 41–42, Online Supplement C.2)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Scheme_Model

namespace ConstrNestedLogit.Scheme

/-- Lemma 8, p. 40 (per-`u` form; proof in Online Supplement C.2, pp. 41–42): let `q ≥ 2`. For
every `u ≥ 0` there is a set `J` of at most `q` products such that problem (17) at `(u, J)` has
an optimal solution with at most one fractional component and, for every such optimal solution
`x`, the rounded-down assortment `⌊x⌋` is feasible for problem (10) and
`q/(q − 1)`-approximate: `∑_{j ∈ S} v_ij (r_ij − u) ≤ (q/(q − 1)) ∑_{j ∈ ⌊x⌋} v_ij (r_ij − u)`
for every space-feasible `S`. -/
theorem lemma_8 {ι : Type*} {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (hw : ∀ i j, 0 < w i j) (hc : ∀ i, 0 ≤ c i) (i : ι) (q : ℕ) (hq : 2 ≤ q)
    (u : ℝ) (hu : 0 ≤ u) :
    ∃ J : Finset (Fin n), J.card ≤ q ∧ (∃ x, optimal17 I w c i u J x ∧ (fractional x).card ≤ 1) ∧
      ∀ x, optimal17 I w c i u J x → (fractional x).card ≤ 1 →
        ConstrNestedLogit.Space.spaceFeasible w c i (roundDown x) ∧
          ∀ S, ConstrNestedLogit.Space.spaceFeasible w c i S →
            obj10 I i u S ≤ ((q : ℝ) / ((q : ℝ) - 1)) * obj10 I i u (roundDown x) := by sorry

end ConstrNestedLogit.Scheme
