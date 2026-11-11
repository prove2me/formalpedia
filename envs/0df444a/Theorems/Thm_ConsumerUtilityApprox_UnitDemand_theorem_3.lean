-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_theorem_3
-- name    : ConsumerUtilityApprox.UnitDemand.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:56:16.381114+00:00
-- url     : https://prove2.me/theorems/2b15b717-35dc-4d7f-99ab-c550c8947272
-- title:
--   Theorem 3 — a polynomial-time BIC, ex-post IR, matching-feasible mechanism with U ≥ OPT^{n,m}/(2e/(e − 1) + (e/(e − 1))² + ε)
-- statement:
--   There are one program $P$ for the oracle real RAM of §2.4 and universal constants $C,k$ such that the following holds. For every $n\ge1$ buyers and $m\ge1$ items, every instance (independent values $V_{ij}\sim F_{ij}$ on $[0,\infty)$ with $0<\mathbb E[V_{ij}]<\infty$, atoms allowed), every $\varepsilon>0$ and every valid oracle ($\mathrm{OPT}^{1,1}$ values with an implementing law on at most two prices; exact expected utilities, request probabilities and means), $P$ on input $(n,m,\varepsilon)$ halts after at most $C(n+m+1/\varepsilon)^k+C$ executed instructions, oracle calls included, and outputs a description of a posted-price/free-lottery mechanism with fair contention resolution whose mechanism $M^{n,m}_{\mathrm{het}}$ is BIC (all types and reports in $\mathbb R^m_+$), ex-post individually rational, matching-feasible in every realized outcome, has nonnegative payments in every realized outcome, and satisfies
--   $$U(M^{n,m}_{\mathrm{het}})\ \ge\ \frac{\mathrm{OPT}^{n,m}}{\dfrac{2e}{e-1}+\Big(\dfrac{e}{e-1}\Big)^2+\varepsilon},$$
--   where $\mathrm{OPT}^{n,m}$ is the supremum of residual surplus over all feasible, BIC, interim individually rational mechanisms with nonnegative payments. The constant is $\frac{2e}{e-1}+(\frac{e}{e-1})^2\approx5.667$. This is the paper's main result: the first constant-factor approximation to optimal consumer utility (money burning) for multiple items and buyers with independent values.
--
--   Differences from the source:
--   - reading: the mechanism can be computed using polynomially many oracle calls and polynomial additional computation in n, m, 1/ε, given oracle access to OPT^{1,1} and exact evaluation → one program P on the oracle real RAM and universal C, k: for every n, m ≥ 1, instance, ε > 0 and every valid oracle, P halts within C·(n + m + 1/ε)^k + C instructions (oracle calls included) and outputs a description decoding to the mechanism; reason: the computational model of §2.4 made explicit; C, k are fixed before the instance
--   - reading: the demand-weight procedure's mechanism (rounds of posted prices and free lotteries, participation, contention) → the output is any MechDescription; its semantics MechDescription.law / preLaw is the paper's family of mechanisms; reason: the procedure is what P computes; the statement fixes the family and the properties of its output
--   - encoding: a randomized mechanism with realized outcomes → RandMech: for each reported profile a PMF over (assignment, payments); BIC and U from its reduced form; reason: the mechanisms use finitely many random choices
--   - encoding: OPT^{n,m}: supremum over feasible (lotteries over matchings), BIC, interim IR mechanisms with nonnegative payments → OPT: sSup over reduced forms that are doubly substochastic, BIC and interim IR for all types in ℝ^m_+, p ≥ 0, with measurable rules and finite interim payments; reason: Birkhoff–von Neumann; measurability is the tacit convention that defines U
--   - encoding: values in R_+, laws F_j, items 1..m → ℝ≥0, ProbabilityMeasure ℝ≥0, Fin m; product law vecLaw; reason: Lean conventions for the same objects
--   - encoding: matching-feasible, ex-post IR, nonnegative payments in every realized outcome → for every reported profile, every outcome in the support of the outcome PMF; reason: realized outcomes are those of positive probability
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 26, Theorem 3 (proof pp. 26–27)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Machine
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem theorem_3 :
    ∃ (P : List Instr) (C k : ℕ), ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
      ∀ (I : Instance n m) (ε : ℝ), 0 < ε → ∀ Ω : List ℝ → List ℝ, IsValidOracle I Ω →
        ∃ (out : List ℝ) (D : MechDescription n m),
          HaltsWithin Ω P n m ε ((C : ℝ) * ((n : ℝ) + m + 1 / ε) ^ k + C) out ∧
          decodeDescription n m out = some D ∧
          D.law.IsBIC I ∧ D.law.IsExPostIR ∧ D.law.IsMatchingFeasible ∧
          D.law.HasNonnegPayments ∧
          OPT I / (2 * Real.exp 1 / (Real.exp 1 - 1) + (Real.exp 1 / (Real.exp 1 - 1)) ^ 2 + ε)
            ≤ D.law.U I := by sorry

end ConsumerUtilityApprox.UnitDemand
