-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_lemma_6
-- name    : ConsumerUtilityApprox.UnitDemand.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:56:24.336966+00:00
-- url     : https://prove2.me/theorems/121381b5-d086-40d0-8bad-92e146adf47c
-- title:
--   Lemma 6 — the averaged, participation-reduced mechanism M̄^{n,m}_het is ex-ante feasible and (1/(2 + e/(e − 1)) − ε)-optimal, computable in poly(n, m, 1/ε)
-- statement:
--   There are one program $P$ for the oracle real RAM of §2.4 and universal constants $C,k$ such that, for every $n,m\ge1$, every instance (independent $V_{ij}\sim F_{ij}$ on $[0,\infty)$, $0<\mathbb E[V_{ij}]<\infty$), every $\varepsilon>0$ and every valid oracle, $P$ on input $(n,m,\varepsilon)$ halts after at most $C(n+m+1/\varepsilon)^k+C$ executed instructions with a mechanism description $D$ whose number of rounds is $T\le Cn^4m^4/\varepsilon^2+C$ and whose pre-contention mechanism $\bar M^{n,m}_{\mathrm{het}}$ (each buyer independently: participate with probability $\rho$, a uniform round, the round's posted-price or free-lottery offer, every request granted) is ex-ante feasible, $\sum_iq^{\mathrm{alloc}}_{ij}\le1$ for every item, and satisfies
--   $$U(\bar M^{n,m}_{\mathrm{het}})\ \ge\ \Big(\frac1{2+e/(e-1)}-\varepsilon\Big)\mathrm{OPT}^{n,m}.$$
--
--   Differences from the source:
--   - reading: the mechanism can be computed using polynomially many oracle calls and polynomial additional computation in n, m, 1/ε, given oracle access to OPT^{1,1} and exact evaluation → one program P on the oracle real RAM and universal C, k: for every n, m ≥ 1, instance, ε > 0 and every valid oracle, P halts within C·(n + m + 1/ε)^k + C instructions (oracle calls included) and outputs a description decoding to the mechanism; reason: the computational model of §2.4 made explicit; C, k are fixed before the instance
--   - reading: the demand-weight procedure's mechanism (rounds of posted prices and free lotteries, participation, contention) → the output is any MechDescription; its semantics MechDescription.law / preLaw is the paper's family of mechanisms; reason: the procedure is what P computes; the statement fixes the family and the properties of its output
--   - encoding: a randomized mechanism with realized outcomes → RandMech: for each reported profile a PMF over (assignment, payments); BIC and U from its reduced form; reason: the mechanisms use finitely many random choices
--   - encoding: OPT^{n,m}: supremum over feasible (lotteries over matchings), BIC, interim IR mechanisms with nonnegative payments → OPT: sSup over reduced forms that are doubly substochastic, BIC and interim IR for all types in ℝ^m_+, p ≥ 0, with measurable rules and finite interim payments; reason: Birkhoff–von Neumann; measurability is the tacit convention that defines U
--   - encoding: after T = O(n^4 m^4/ε^2) rounds → D.T ≤ C·n^4 m^4/ε^2 + C with the same universal C; reason: explicit constant for O(·) (the proof uses T = ⌈4n^4m^4/ε^2⌉)
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 25, Lemma 6 (restated and proved pp. 44–48, Appendix C.4)

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

theorem lemma_6 :
    ∃ (P : List Instr) (C k : ℕ), ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
      ∀ (I : Instance n m) (ε : ℝ), 0 < ε → ∀ Ω : List ℝ → List ℝ, IsValidOracle I Ω →
        ∃ (out : List ℝ) (D : MechDescription n m),
          HaltsWithin Ω P n m ε ((C : ℝ) * ((n : ℝ) + m + 1 / ε) ^ k + C) out ∧
          decodeDescription n m out = some D ∧
          (D.T : ℝ) ≤ (C : ℝ) * (n : ℝ) ^ 4 * (m : ℝ) ^ 4 / ε ^ 2 + C ∧
          D.preLaw.reduced.IsExAnteFeasible I ∧
          (1 / (2 + Real.exp 1 / (Real.exp 1 - 1)) - ε) * OPT I ≤ D.preLaw.U I := by sorry

end ConsumerUtilityApprox.UnitDemand
