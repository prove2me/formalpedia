-- Prove2me | Theorems.Thm_CausalFailureRank_Supplement_theorem_D_9
-- name    : CausalFailureRank.Supplement.theorem_D_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:54:16.38822+00:00
-- url     : https://prove2.me/theorems/4c213f3f-784f-4410-b293-5de6de910700
-- title:
--   Theorem D.9 — paid overlay
-- statement:
--   In the cap-relaxed rational homogeneous shared-pool model, fix $0<\delta\le1/64$. For every finite-cost free-correction policy $\pi_0$, there exists a current-payment policy $\pi_f$ with no larger failure probability and
--
--   $$
--   \mathbb E C(\pi_f)\le \mathbb E C_{\mathrm{obs}}(\pi_0)
--     +\frac{17}{2}Na\log(1+f/a).
--   $$
--
--   Consequently,
--
--   $$
--   V_f^\infty(\delta)\le V_0^\infty(\delta)+9D_f.
--   $$
--
--   The simulator retains current payment: every genuine correction is physically executed and charged before advance, including on paths that later fail. This is only a cap-relaxed comparison and makes no native stopping-time claim.
--
--   Differences from the source:
--   - encoding: expected costs and values that may be infinite → lower integrals and infima in $[0,\infty]$; reason: the finite-cost hypothesis is stated as inequality with $+\infty$, and extended nonnegative values preserve all nonnegative charges without defaulting
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), Theorem D.9, pp.29–30 (PDF pp.30–31), eqs. (41)–(42)

import Mathlib
import Definitions.Def_CausalFailureRank_Supplement_paidModel

set_option autoImplicit false

namespace CausalFailureRank
namespace Supplement

/-- **Theorem D.9 (Paid overlay).** Zang, Li, Jin, Xu, *Causal Failure Rank Determines
Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…),
Theorem D.9, pp.29–30 (PDF pp.30–31), equations (41)–(42).

Every finite-cost cap-relaxed free-correction policy has a cap-relaxed current-payment overlay
with no larger failure probability and the stated additive review-and-fee bound. Consequently the
paid relaxed value is at most the free relaxed value plus `9 D_f`.

**Formalization Note.** This theorem deliberately uses `relaxedCaps`; it makes no native stopping-
time claim. The free and paid instances have identical facts, channels, compatibilities, review
prices, and normal-call accounting and differ only in their correction fee. `expectedObsBill`
counts reviews alone, and the produced policy uses the base model's genuine `currentPay` execution,
so corrections on paths that later fail are still physically executed and charged. -/
theorem theorem_D_9 {N K : ℕ} (M : PaidModel N K) (δ : ℚ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 64) :
    (∀ π₀ : Policy (freeInstance M),
      expBill (freeInstance M) .currentPay (relaxedCaps N) π₀ ≠ ⊤ →
      ∃ πf : Policy M.I,
        failProb M.I .currentPay (relaxedCaps N) πf ≤
          failProb (freeInstance M) .currentPay (relaxedCaps N) π₀ ∧
        expBill M.I .currentPay (relaxedCaps N) πf ≤
          expectedObsBill (freeInstance M) (relaxedCaps N) π₀ +
            ENNReal.ofReal ((17 / 2 : ℝ) * N * scaleA M *
              Real.log (1 + M.fee / scaleA M))) ∧
    relaxedValue M δ ≤ relaxedFreeValue M δ + 9 * feeScale M := by sorry

end Supplement
end CausalFailureRank
