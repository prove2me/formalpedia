-- Prove2me | Theorems.Thm_CausalFailureRank_Supplement_theorem_D_1
-- name    : CausalFailureRank.Supplement.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:53:22.446013+00:00
-- url     : https://prove2.me/theorems/64545140-838a-4ee3-b4af-fbef979d2ec3
-- title:
--   Theorem D.1 — separation of correction prices
-- statement:
--   In the rational homogeneous shared-pool model with $K<N$, fair facts, BSC reviews of accuracy $1/2+\gamma$ and price $c$, correction price $f$, and the current-payment contract, assume $0<\delta\le1/64$ and the native resource certificate (29) using the explicit $Q$ of (34). Let
--
--   $$
--   A=V_0^{\mathrm{nat}}(\delta),\quad
--   D_f=aN\log(1+f/a),\quad
--   S_\delta=aN\log(1+N/\delta),\quad
--   T=\min\{A+D_f,S_\delta\}.
--   $$
--
--   Here $A$ uses the same current-payment contract, original quotas, call cap, and target risk. Then
--
--   $$
--   \frac{T}{129}\le V_f^{\mathrm{nat}}(\delta)\le72T.
--   $$
--
--   The constants are uniform over every parameter and native resource choice. One rational algorithm, whose inputs contain neither $A$ nor an optimal free policy, returns a native $\delta$-safe initial mixture of at most two finite-state policies with exactly calibrated bounded local tests and
--
--   $$
--   V_f^\infty(\delta)\le V_f^{\mathrm{nat}}(\delta)
--     \le \mathbb E C_{\mathrm{alg}}\le8V_f^\infty(\delta).
--   $$
--
--   Its operation and bit bounds are stated in Theorem D.10; dependence polynomial in $\log(1/\gamma)$ is not claimed.
--
--   Differences from the source:
--   - encoding: real-valued infima and expected charges with a possible infeasible class → values in $[0,\infty]$; reason: $+\infty$ faithfully represents the infimum of an empty safe-policy class and no conversion to a junk real value occurs
--   - encoding: the minima and ceilings defining the certificate in (34) and bisection bound (54) → least-natural-number functions plus validity conclusions for every selected minimum and ceiling; reason: this excludes the total-function default for an empty minimizing set while retaining the printed certificate and termination bound
--   - encoding: the explicit rational algorithm and its two-policy, bounded-test output → one uniform Lean function on rational public inputs together with finite-state mixture and exact rational calibration certificates; reason: the function takes neither the free value nor a free policy and preserves the source's computational output interface
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), Theorem D.1, pp.23–24 (PDF pp.24–25), eqs. (29)–(32)

import Mathlib
import Definitions.Def_CausalFailureRank_Supplement_paidModel

set_option autoImplicit false

namespace CausalFailureRank
namespace Supplement

/-- **Theorem D.1 (Separation of correction prices).** Zang, Li, Jin, Xu, *Causal Failure Rank
Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256
721c8b0d…), Theorem D.1, pp.23–24 (PDF pp.24–25), equations (29)–(32).

The same explicit rational algorithm works uniformly for every rational homogeneous shared-pool
instance. Its inputs do not include the free value `A` or an optimal free policy. Under the exact
resource certificate (34), it produces a native safe policy and the complete eight-factor chain,
while the native paid value lies between the printed universal multiples of
`min {A + D_f, S_δ}`.

**Formalization Note.** `nativeFreeValue` is the free value under the same `currentPay` contract,
original quotas, call cap, and risk; `relaxedValue` removes only review and call caps. All values
are in `ℝ≥0∞`, so infeasible policy classes retain value `⊤`. Rationality is retained rather than
generalized to arbitrary real data. The operation and bit-complexity interface is made explicit in
Theorem D.10; no polynomial dependence on `log(1/γ)` is asserted. -/
theorem theorem_D_1 :
    ∃ alg : RationalNativeAlgorithm,
      ∀ (N K : ℕ) (M : PaidModel N K) (caps : Caps N) (δ : ℚ),
        0 < δ → δ ≤ 1 / 64 → ResourceQualified M caps δ →
        CertificateValid M δ ∧
        BisectionBoundValid M δ ∧
        comparisonScale M caps δ / 129 ≤ nativeValue M caps δ ∧
        nativeValue M caps δ ≤ 72 * comparisonScale M caps δ ∧
        failProb M.I .currentPay caps (alg.run M caps δ) ≤ ENNReal.ofReal δ ∧
        relaxedValue M δ ≤ nativeValue M caps δ ∧
        nativeValue M caps δ ≤ expBill M.I .currentPay caps (alg.run M caps δ) ∧
        expBill M.I .currentPay caps (alg.run M caps δ) ≤ 8 * relaxedValue M δ ∧
        IsTwoPolicyOutput M caps δ (alg.calibration M caps δ) (alg.run M caps δ) ∧
        (alg.work M caps δ).Correct M δ := by sorry

end Supplement
end CausalFailureRank
