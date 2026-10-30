-- Prove2me | Theorems.Thm_FarmerInfoProvision_proposition_2_proof_one_minus_zero
-- name    : FarmerInfoProvision.proposition_2_proof_one_minus_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:49:01.964751+00:00
-- url     : https://prove2.me/theorems/074fd52a-15d2-4c93-aee8-a42d694f0b49
-- title:
--   Proof of Proposition 2: $W(1)-W(0)=\beta V(n,\beta;\gamma)/(\cdots)$
-- statement:
--   Let $W$ be the total welfare built from Lemma 2's closed forms and $V(n,\beta;\gamma)$ the provision index of Proposition 2. For $n\ge4$, $a,b,\alpha,\beta>0$ and $\gamma\ge0$,
--
--   $$
--   W(1,\beta;\gamma)-W(0,\beta;\gamma)=\frac{\beta\,V(n,\beta;\gamma)}{b(2\alpha+\gamma+n\gamma)^2\bigl[4\alpha^2+(1+n)\gamma(\beta+\gamma)+2\alpha\bigl(2\beta+(2+n)\gamma\bigr)\bigr]^2}.
--   $$
--
--   Since the denominator is positive, informing one farmer beats informing nobody exactly when $V>0$; this is where the case split of Proposition 2 comes from.
--
--   Differences from the source:
--   - encoding: the closed forms contain 1/γ, undefined at γ = 0 → Lean's 1/0 = 0, multiplied by A1² = B1² = 0; reason: at γ = 0 the formulas take their γ → 0 limits, so γ = 0 (no private signal) is covered with its intended values
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 36

import Mathlib
import Definitions.Def_FarmerInfoProvision_totalWelfare
import Definitions.Def_FarmerInfoProvision_provisionIndex

namespace FarmerInfoProvision

/-- **Proof of Proposition 2: `W(1) − W(0) = βV(n, β; γ)/(…)`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 36:
"comparing it with the benchmark case without the public signal, we find that:
`W(1, β; γ) − W(0, β; γ) = βV(n, β; γ) / (b(2α + γ + nγ)² [4α² + (1 + n)γ(β + γ) +
2α(2β + (2 + n)γ)]²)`, which is not necessarily positive."

For `n ≥ 4` farmers, `b, α, β > 0` and `γ ≥ 0`, the closed-form welfare satisfies the printed
identity, with `V = provisionIndex n α β γ`. In particular `W(1) − W(0)` has the sign of `V`.

**Formalization Note.** `W` is Lemma 2's closed form; at `γ = 0` its `1/γ` terms are junk values
multiplied by `0`. -/
theorem proposition_2_proof_one_minus_zero {n : ℕ} (hn : 4 ≤ n) {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    totalWelfare a b c (n : ℝ) 1 α β γ - totalWelfare a b c (n : ℝ) 0 α β γ =
      β * provisionIndex (n : ℝ) α β γ /
        (b * (2 * α + γ + (n : ℝ) * γ) ^ 2 *
          (4 * α ^ 2 + (1 + (n : ℝ)) * γ * (β + γ) + 2 * α * (2 * β + (2 + (n : ℝ)) * γ)) ^ 2) := by sorry

end FarmerInfoProvision
