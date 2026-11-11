-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_eq_5_12
-- name    : ConsumerUtilityApprox.UnitDemand.eq_5_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:55:31.491866+00:00
-- url     : https://prove2.me/theorems/27d64bfd-3437-44aa-ae62-a917965e0e47
-- title:
--   Equation (5.12) — after fair contention the mechanism is BIC, ex-post IR, matching-feasible, has nonnegative payments, and U(M^{n,m}_het) = (1 − 1/e) U(M̄^{n,m}_het)
-- statement:
--   Let an instance have $n,m\ge1$ and independent values $V_{ij}\sim F_{ij}$, $0<\mathbb E[V_{ij}]<\infty$. Let $D$ be a mechanism description whose pre-contention mechanism $\bar M^{n,m}_{\mathrm{het}}$ is ex-ante feasible ($\sum_iq^{\mathrm{alloc}}_{ij}\le1$), whose announced request probabilities are exact, $Q_{ij}=q^{\mathrm{alloc}}_{ij}(\bar M^{n,m}_{\mathrm{het}})$, and whose service probabilities are $\sigma_j=(1-1/e)/c_j$ with $c_j$ from (5.11). Then the mechanism $M^{n,m}_{\mathrm{het}}$ (requests, fair selection per item, service with probability $\sigma_j$, payment only when served) is BIC, ex-post individually rational and matching-feasible in every realized outcome, has nonnegative payments in every realized outcome, and
--   $$U(M^{n,m}_{\mathrm{het}})=\Big(1-\frac1e\Big)U(\bar M^{n,m}_{\mathrm{het}}).$$
--
--   Differences from the source:
--   - encoding: a randomized mechanism with realized outcomes → RandMech: for each reported profile a PMF over (assignment, payments); BIC and U from its reduced form; reason: the mechanisms use finitely many random choices
--   - generalization: M̄^{n,m}_het produced by the demand-weight procedure of §5.1.1 → every mechanism description of the family whose pre-contention mechanism is ex-ante feasible, with exact Q and σ_j = (1 − 1/e)/c_j; reason: the argument (Observation 1, (5.11)) uses only ex-ante feasibility and exact request probabilities; Lemma 6's M̄ is such a description
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 26, equation (5.12) (Appendix C.5, pp. 48–50)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem eq_5_12 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (I : Instance n m)
    (D : MechDescription n m)
    (hfeas : D.preLaw.reduced.IsExAnteFeasible I)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j)
    (hσ : ∀ j, D.σ j = (1 - Real.exp (-1)) / selectionConst D.Q j) :
    D.law.IsBIC I ∧ D.law.IsExPostIR ∧ D.law.IsMatchingFeasible ∧
      D.law.HasNonnegPayments ∧
      D.law.U I = (1 - Real.exp (-1)) * D.preLaw.U I := by sorry

end ConsumerUtilityApprox.UnitDemand
