-- Prove2me | Theorems.Thm_AMPUniversality_StateEvol_proposition_4
-- name    : AMPUniversality.StateEvol.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:32:21.507026+00:00
-- url     : https://prove2.me/theorems/6114d9ce-8dfc-4232-9d0f-f93015c1627f
-- title:
--   Proposition 4 — coordinate moments converge to Gaussian moments
-- statement:
--   For a polynomial and converging AMP sequence, fix a class $a$, a positive iteration time $t$, and a nonnegative multi-index $m$. If the coordinate $i(N)$ eventually belongs to class $a$, then
--
--   $$\lim_{N\to\infty}\mathbb E[(x_{i(N)}^t)^m]=\mathbb E[(Z_a^t)^m],\qquad Z_a^t\sim\mathcal N(0,\Sigma_a^t).$$
--
--   This is the moment identification step of state evolution. The statement also records integrability of the finite-size and Gaussian monomials, so the displayed expectations have their ordinary meaning.
--
--   **Formalization Note** The index sequence is written on sizes $N+1$ to avoid asking for an element of the empty type `Fin 0`; eventual class membership is enough for the limit.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 30, Proposition 4

import Definitions.Def_AMPUniversality_StateEvol_SE

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace AMPUniversality.StateEvol

/-- Proposition 4: fixed-coordinate moments converge to state-evolution moments. -/
theorem proposition_4 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {q h k d : ℕ}
    (M : Model Ω q h k d) (hconv : IsConverging P M)
    (a : Fin k) (i : ∀ N : ℕ, Fin (N + 1))
    (hi : ∀ᶠ N in atTop, M.cls (N + 1) (i N) = a)
    (t : ℕ) (ht : 1 ≤ t) (m : Fin q → ℕ) :
    (∀ N, Integrable
      (fun ω => monomial m (M.orbit (N + 1) ω t (i N))) P) ∧
    Integrable (monomial m) (gaussianVec (M.se t a)) ∧
    Tendsto
      (fun N => ∫ ω, monomial m (M.orbit (N + 1) ω t (i N)) ∂P)
      atTop
      (𝓝 (∫ z, monomial m z ∂(gaussianVec (M.se t a)))) := by sorry

end AMPUniversality.StateEvol
