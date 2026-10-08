-- Prove2me | Theorems.Thm_ConstrNestedLogit_Scheme_case_small_optimal
-- name    : ConstrNestedLogit.Scheme.case_small_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:00.916911+00:00
-- url     : https://prove2.me/theorems/e2204173-0fc9-4d90-918d-31bde8456450
-- title:
--   Case |S*_i| ≤ q: rounding (17) with J = S*_i solves problem (10)
-- statement:
--   Fix a nest $i$ with space requirements $w_{ij}>0$ and capacity $c_i$, a parameter $\hat u\ge 0$ and an integer $q$. Let $S^\ast_i$ be an optimal solution of problem (10) at $u=\hat u$, that is, $\sum_{j\in S^\ast_i}w_{ij}\le c_i$ and $\sum_{j\in S^\ast_i}v_{ij}(r_{ij}-\hat u)\ge\sum_{j\in S}v_{ij}(r_{ij}-\hat u)$ for every $S\in\mathcal C_i$, and suppose $|S^\ast_i|\le q$. If $x$ is an optimal solution of problem (17) at $u=\hat u$ with $J=S^\ast_i$, then $\lfloor x\rfloor=\{j:x_{ij}=1\}$ is feasible for (10) and optimal at $\hat u$:
--
--   $$
--   \sum_{j\in S} v_{ij}(r_{ij}-\hat u)\le\sum_{j\in\lfloor x\rfloor} v_{ij}(r_{ij}-\hat u)\qquad\text{for every } S\in\mathcal C_i .
--   $$
--
--   This is the first case of the proof of Lemma 8: when an optimal assortment is small, the candidate built from $J=S^\ast_i\in\wp_q$ is itself optimal.
--
--   **Formalization Note** The positivity $w_{ij}>0$ is added (the space model divides by $w_{ij}$). The bound $|S^\ast_i|\le q$ records the case of the proof and places $J$ in $\wp_q$; it is not needed for the conclusion.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 41, Online Supplement C.2, proof of Lemma 8, case |S*_i| ≤ q

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Scheme_Model

namespace ConstrNestedLogit.Scheme

/-- Online Supplement C.2, p. 41 (case `|S*_i| ≤ q`): if `S*` is optimal for problem (10) at
`û ≥ 0` and has at most `q` products, then rounding down any optimal solution of problem (17)
with `J = S*` at `û` gives an optimal solution of problem (10) at `û`. -/
theorem case_small_optimal {ι : Type*} {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (hw : ∀ i j, 0 < w i j) (i : ι) (q : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (Sstar : Finset (Fin n)) (hSfeas : ConstrNestedLogit.Space.spaceFeasible w c i Sstar)
    (hSopt : ∀ S, ConstrNestedLogit.Space.spaceFeasible w c i S → obj10 I i u S ≤ obj10 I i u Sstar)
    (hcard : Sstar.card ≤ q)
    (x : Fin n → ℝ) (hx : optimal17 I w c i u Sstar x) :
    ConstrNestedLogit.Space.spaceFeasible w c i (roundDown x) ∧
      ∀ S, ConstrNestedLogit.Space.spaceFeasible w c i S → obj10 I i u S ≤ obj10 I i u (roundDown x) := by sorry

end ConstrNestedLogit.Scheme
