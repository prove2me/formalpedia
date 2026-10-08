-- Prove2me | Theorems.Thm_ConstrNestedLogit_Scheme_zstar_le_zeta
-- name    : ConstrNestedLogit.Scheme.zstar_le_zeta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:23.599368+00:00
-- url     : https://prove2.me/theorems/791f5e20-ad3a-4df9-9cd6-ca715b2b34be
-- title:
--   z*(û) ≤ ζ*(û, J*_i): an optimal solution of (10) is feasible for (17)
-- statement:
--   Fix a nest $i$, a parameter $\hat u\ge0$ and an integer $q$. Let $S^\ast_i$ be an optimal solution of problem (10) at $\hat u$ with $|S^\ast_i|>q$, and let $J^\ast_i\subseteq S^\ast_i$ consist of $q$ products of $S^\ast_i$ with the largest utilities. Then the indicator vector of $S^\ast_i$ is feasible for problem (17) at $u=\hat u$, $J=J^\ast_i$, and consequently, writing $\zeta^\ast(\hat u,J^\ast_i)$ for the optimal value of (17),
--
--   $$
--   z^\ast(\hat u)=\sum_{j\in S^\ast_i}v_{ij}(r_{ij}-\hat u)\le\zeta^\ast(\hat u,J^\ast_i).
--   $$
--
--   The relaxation (17) with $J=J^\ast_i$ therefore loses nothing against problem (10).
--
--   **Formalization Note** $\zeta^\ast(\hat u,J^\ast_i)$ is represented by the objective value of an arbitrary optimal solution of (17); the feasibility of $S^\ast_i$ is stated explicitly so that the bound is not vacuous.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 42, Online Supplement C.2, proof of Lemma 8 (claim z*(û) ≤ ζ*(û, J*_i))

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Scheme_Model

namespace ConstrNestedLogit.Scheme

/-- Online Supplement C.2, p. 42, the claim `z*(û) ≤ ζ*(û, J*_i)`: let `S*` be optimal for
problem (10) at `û ≥ 0` with `|S*| > q`, and let `J*` consist of `q` products of `S*` with the
largest utilities. Then (the indicator vector of) `S*` is feasible for problem (17) at
`(û, J*)`, and consequently `z*(û) = ∑_{j ∈ S*} v_ij (r_ij − û)` is at most the objective value
of every optimal solution of (17) at `(û, J*)`. -/
theorem zstar_le_zeta {ι : Type*} {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (i : ι) (q : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (Sstar : Finset (Fin n)) (hSfeas : ConstrNestedLogit.Space.spaceFeasible w c i Sstar)
    (hSopt : ∀ S, ConstrNestedLogit.Space.spaceFeasible w c i S → obj10 I i u S ≤ obj10 I i u Sstar)
    (hcard : q < Sstar.card)
    (Jstar : Finset (Fin n)) (hJsub : Jstar ⊆ Sstar) (hJcard : Jstar.card = q)
    (hJtop : ∀ j ∈ Jstar, ∀ k ∈ Sstar \ Jstar, ConstrNestedLogit.Space.utility I i u k ≤ ConstrNestedLogit.Space.utility I i u j) :
    feasible17 I w c i u Jstar (fun j => if j ∈ Sstar then 1 else 0) ∧
      ∀ x, optimal17 I w c i u Jstar x → obj10 I i u Sstar ≤ obj17 I i u x := by sorry

end ConstrNestedLogit.Scheme
