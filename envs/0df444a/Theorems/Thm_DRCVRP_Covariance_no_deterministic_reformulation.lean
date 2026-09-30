-- Prove2me | Theorems.Thm_DRCVRP_Covariance_no_deterministic_reformulation
-- name    : DRCVRP.Covariance.no_deterministic_reformulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:38:06.686702+00:00
-- url     : https://prove2.me/theorems/048ce775-a101-46e9-afa4-23bd59fb87f4
-- title:
--   Theorem 6 — no deterministic CVRP has the same feasible route sets
-- statement:
--   There is an instance of the distributionally robust capacitated vehicle routing problem with the covariance ambiguity set (16) — a number $n$ of customers, $m$ vehicles of capacity $Q\ge0$, a risk level $\epsilon\in(0,1)$, a box $[\underline{\boldsymbol q},\overline{\boldsymbol q}]$ with $\underline{\boldsymbol q}\ge\mathbf 0$, a mean $\boldsymbol\mu$ in its interior and a covariance bound $\Sigma\succ0$ — such that for every deterministic instance on the same customers and fleet, with capacity $Q'\ge0$ and demands $\boldsymbol q\ge\mathbf 0$,
--   $$
--   \big\{\boldsymbol R\in\mathfrak P(V_C,m):\ \boldsymbol R\text{ feasible in RVRP}(\mathcal P)\big\}\ne\big\{\boldsymbol R\in\mathfrak P(V_C,m):\ \textstyle\sum_{i\in R_k}q_i\le Q'\ \forall k\big\}.
--   $$
--
--   In words, the chance constraints over a covariance ambiguity set cannot, in general, be replaced by deterministic capacity constraints with suitably chosen demands and capacity. This is why the paper works with the demand estimator $d_{\mathcal P}$ instead of a deterministic surrogate.
--
--   **Formalization Note** Route sets, RVRP($\mathcal P$)-feasibility and deterministic feasibility are the definitions `IsRouteSet`, `RVRPFeasible` and `DetFeasible`. "The same set of feasible route sets" is equality of the two sets of route sets `Fin m → List (Fin n)`. The instance is required to satisfy all side conditions of (16).
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §5.2, p. 727, Theorem 6

import Mathlib
import Definitions.Def_DRCVRP_Covariance_AmbiguitySet
import Definitions.Def_DRCVRP_Covariance_Routing

open MeasureTheory

namespace DRCVRP.Covariance

/-- Theorem 6 (p. 727): for some instance of the distributionally robust CVRP with the
covariance ambiguity set (16) — customers `n`, vehicles `m`, capacity `Q ≥ 0`, risk level
`ε ∈ (0,1)`, box `[q̲, q̄]` with `q̲ ≥ 0`, mean `μ ∈ int [q̲, q̄]` and `Σ ≻ 0` — no deterministic
CVRP instance with the same customers and fleet (capacity `Q' ≥ 0`, demands `q ≥ 0`) has the same
set of feasible route sets. -/
theorem no_deterministic_reformulation :
    ∃ (n m : ℕ) (Q ε : ℝ) (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ),
      0 ≤ Q ∧ 0 < ε ∧ ε < 1 ∧ (∀ j, 0 ≤ qlo j) ∧ (∀ j, qlo j < μ j ∧ μ j < qhi j) ∧
      Sig.PosDef ∧
      ∀ (Q' : ℝ) (q : Fin n → ℝ), 0 ≤ Q' → (∀ j, 0 ≤ q j) →
        {R : Fin m → List (Fin n) | RVRPFeasible (covarianceSet qlo qhi μ Sig) ε Q R} ≠
          {R | DetFeasible Q' q R} := by sorry

end DRCVRP.Covariance
