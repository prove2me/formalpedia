-- Prove2me | Theorems.Thm_CausalFailureRank_Supplement_theorem_D_10
-- name    : CausalFailureRank.Supplement.theorem_D_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:54:40.824808+00:00
-- url     : https://prove2.me/theorems/b2b51ffc-6d43-4b1a-ae1b-5c6b532cc467
-- title:
--   Theorem D.10 — native eight-factor algorithm
-- statement:
--   In every rational homogeneous shared-pool current-payment instance with $0<\delta\le1/64$, let $t_0,B,\Lambda,\varepsilon,p_m,M,E,Q$ be exactly the quantities of equation (34). If every stage admits $Q$ reviews and
--
--   $$
--   H\ge H_0+NQ+K,
--   $$
--
--   one uniform rational algorithm produces a native $\delta$-safe policy satisfying
--
--   $$
--   V_f^\infty(\delta)\le V_f^{\mathrm{nat}}(\delta)
--     \le \mathbb E C_{\mathrm{alg}}\le8V_f^\infty(\delta).
--   $$
--
--   The output is an initial mixture of at most two whole finite-state policies. For every positive boundary level $m\le M$, a rationally computed capped test has error $q_m<p_m$ and is mixed with a blind guess using
--
--   $$
--   \omega_m=\frac{1/2-p_m}{1/2-q_m},
--   $$
--
--   preserving the endpoint error exactly. There are at most $J_{\mathrm{bis}}+2$ penalty solves. Universal constants bound one solve by $O(N(K+1)(M+1))$ rational operations, stored records by $O(N(K+1))$, and calibration by $O(Q(M+1)^2)$ rational updates; the statement also records the paper's additive bit-length bound. Since $Q$ displays numerical dependence on $1/\gamma$, no polynomial dependence on $\log(1/\gamma)$ is asserted.
--
--   Differences from the source:
--   - encoding: the minima and ceilings in equations (34) and (54) → least-natural-number functions plus validity conclusions for every selected minimum and ceiling; reason: this rules out Lean's total-function value on an empty minimization set while retaining exactly the printed certificate and bisection bound
--   - encoding: the explicit rational implementation and complexity paragraph → a uniform rational-input policy function, finite-state/calibration certificates, and universal operation, storage, and bit-length inequalities; reason: these expose the same algorithmic guarantees as propositions without narrowing the policy comparator
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), Theorem D.10 and Appendix D.2.5, pp.30–33 (PDF pp.31–34), eqs. (29), (32), (34), (46)–(56)

import Mathlib
import Definitions.Def_CausalFailureRank_Supplement_paidModel

set_option autoImplicit false

namespace CausalFailureRank
namespace Supplement

/-- **Theorem D.10 (Native eight-factor algorithm).** Zang, Li, Jin, Xu, *Causal Failure Rank
Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256
721c8b0d…), Theorem D.10, pp.30–33 (PDF pp.31–34), equations (29), (32), (34), and the complexity
paragraph of Appendix D.2.5.

The explicit certificate (34) and one rational algorithm produce, under (29), a native `δ`-safe
policy costing at most eight times the cap-relaxed optimum. The output is an initial mixture of at
most two whole finite-state policies and uses bounded local tests calibrated to preserve the exact
endpoint errors. The displayed operation bounds are uniform.

**Formalization Note.** The universal algorithm and complexity constants precede every input, so
they cannot depend on the instance. The calibration interface contains the exact rational formula
(56), not merely an approximate error guarantee. The complexity bound is polynomial in the
displayed numerical parameters `N,K,M,Q` and in the number of penalty solves; because `Q` contains
ceilings in `1/γ` and `1/γ²`, this does not assert polynomial dependence on `log(1/γ)`. -/
theorem theorem_D_10 :
    ∃ alg : RationalNativeAlgorithm, ∃ Cop Cstore Ccal Cbit : ℕ,
      0 < Cop ∧ 0 < Cstore ∧ 0 < Ccal ∧ 0 < Cbit ∧
      ∀ (N K : ℕ) (M : PaidModel N K) (caps : Caps N) (δ : ℚ),
        0 < δ → δ ≤ 1 / 64 → ResourceQualified M caps δ →
        CertificateValid M δ ∧
        BisectionBoundValid M δ ∧
        failProb M.I .currentPay caps (alg.run M caps δ) ≤ ENNReal.ofReal δ ∧
        relaxedValue M δ ≤ nativeValue M caps δ ∧
        nativeValue M caps δ ≤ expBill M.I .currentPay caps (alg.run M caps δ) ∧
        expBill M.I .currentPay caps (alg.run M caps δ) ≤ 8 * relaxedValue M δ ∧
        IsTwoPolicyOutput M caps δ (alg.calibration M caps δ) (alg.run M caps δ) ∧
        (alg.work M caps δ).Correct M δ ∧
        (alg.work M caps δ).penaltyRationalOps ≤
          Cop * (alg.work M caps δ).penaltySolves * N * (K + 1) * (certM M δ + 1) ∧
        (alg.work M caps δ).storedRecords ≤ Cstore * N * (K + 1) ∧
        (alg.work M caps δ).calibrationRationalOps ≤
          Ccal * certQ M δ * (certM M δ + 1) ^ 2 ∧
        (alg.work M caps δ).probabilityBitLength ≤
          Cbit * ((N + 1) * (certM M δ + 1) *
              ((alg.work M caps δ).menuInputBitLength + 1) +
            certQ M δ * ((alg.work M caps δ).gammaInputBitLength + 1) +
            (alg.work M caps δ).deltaInputBitLength +
            (alg.work M caps δ).multiplierBitLength + 1) := by sorry

end Supplement
end CausalFailureRank
