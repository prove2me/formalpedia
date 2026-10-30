-- Prove2me | Theorems.Thm_FarmerInfoProvision_proposition_2_proof_one_beats_two
-- name    : FarmerInfoProvision.proposition_2_proof_one_beats_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:48:09.870456+00:00
-- url     : https://prove2.me/theorems/c50071e1-1793-4a16-8d31-32cf9179bf95
-- title:
--   Proof of Proposition 2: informing one farmer beats informing two (corrected: the printed difference omits its denominator)
-- statement:
--   Let $W$ be the total welfare built from Lemma 2's closed forms and $\Psi(m)$ Proposition 1's normalizing constant at $n_1=m$. For $n\ge4$, $a,b,\alpha,\beta>0$ and $\gamma\ge0$:
--
--   1. the welfare difference is
--   $$
--   W(1,\beta;\gamma)-W(2,\beta;\gamma)=\frac{\beta\,\{\cdots\}}{b\,(\Psi(1)/2)^2\,\Psi(2)^2},
--   $$
--   where $\beta\{\cdots\}$ is the expression printed in the proof,
--   $$
--   \begin{aligned}
--   \beta\Bigl\{&64\alpha^6+64\alpha^5(3\beta+4n\gamma)+(1+n)\gamma^3(\beta+\gamma)\bigl(4(-3+n)\beta^2+4(-5+3n)\beta\gamma+(-5+7n)\gamma^2\bigr)\\
--   &+16\alpha^4\bigl(12\beta^2+(-1+33n)\beta\gamma+(-15+34n+7n^2)\gamma^2\bigr)\\
--   &+4\alpha\gamma^2\bigl(4(-4+n)\beta^3+2(-25+4n+7n^2)\beta^2\gamma+(-47+11n+29n^2)\beta\gamma^2+2(-6+4n+7n^2)\gamma^3\bigr)\\
--   &+32\alpha^3\bigl(2\beta^3+(-1+9n)\beta^2\gamma+(-16+25n+5n^2)\beta\gamma^2+(-10+14n+7n^2)\gamma^3\bigr)\\
--   &+4\alpha^2\gamma\bigl(4(-1+n)\beta^3+4(-21+17n+3n^2)\beta^2\gamma+(-126+95n+59n^2)\beta\gamma^2+(-45+44n+42n^2)\gamma^3\bigr)\Bigr\};
--   \end{aligned}
--   $$
--   2. $W(2,\beta;\gamma)<W(1,\beta;\gamma)$.
--
--   If the public signal is provided at all, it should go to exactly one farmer.
--
--   Differences from the source:
--   - correction: W(1, β; γ) − W(2, β; γ) = β{…} (the printed bracket) → W(1) − W(2) = β{…} / (b (Ψ(1)/2)² Ψ(2)²); reason: the printed display is only the numerator: at n = 4, α = β = γ = b = 1 the difference is 217/43350 while β{…} = 32550; the omitted denominator is positive, so the sign claim is unaffected
--   - encoding: the closed forms contain 1/γ, undefined at γ = 0 → Lean's 1/0 = 0, multiplied by A1² = B1² = 0; reason: at γ = 0 the formulas take their γ → 0 limits, so γ = 0 (no private signal) is covered with its intended values
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 36

import Mathlib
import Definitions.Def_FarmerInfoProvision_Psi
import Definitions.Def_FarmerInfoProvision_totalWelfare

namespace FarmerInfoProvision

/-- **Proof of Proposition 2: informing one farmer beats informing two.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 36:
"we obtain the welfare difference `W(1, β; γ) − W(2, β; γ)` as: `β{64α⁶ + 64α⁵(3β + 4nγ)
+ (1 + n)γ³(β + γ)(4(−3 + n)β² + 4(−5 + 3n)βγ + (−5 + 7n)γ²)
+ 16α⁴(12β² + (−1 + 33n)βγ + (−15 + 34n + 7n²)γ²)
+ 4αγ²(4(−4 + n)β³ + 2(−25 + 4n + 7n²)β²γ + (−47 + 11n + 29n²)βγ² + 2(−6 + 4n + 7n²)γ³)
+ 32α³(2β³ + (−1 + 9n)β²γ + (−16 + 25n + 5n²)βγ² + (−10 + 14n + 7n²)γ³)
+ 4α²γ(4(−1 + n)β³ + 4(−21 + 17n + 3n²)β²γ + (−126 + 95n + 59n²)βγ² + (−45 + 44n + 42n²)γ³)}`,
which is positive as long as `n ≥ 4`."

For `n ≥ 4` farmers, `b, α, β > 0` and `γ ≥ 0`:
1. `W(1, β; γ) − W(2, β; γ)` equals the printed bracket `β{…}` divided by
   `b (Ψ(1)/2)² Ψ(2)²`, where `Ψ(m) = Psi n m α β γ` is Proposition 1's `Ψ` at `n1 = m`;
2. `W(2, β; γ) < W(1, β; γ)`.

**Formalization Note.** The printed display gives only the numerator: the difference is the
bracket divided by the positive number `b(Ψ(1)/2)²Ψ(2)²`, which the page omits. For example,
at `n = 4`, `α = β = γ = b = 1` the difference is `217/43350`, while the bracket is `32550`. The
sign, which is what the proof uses, is unaffected. `W` is Lemma 2's closed form. -/
theorem proposition_2_proof_one_beats_two {n : ℕ} (hn : 4 ≤ n) {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    totalWelfare a b c (n : ℝ) 1 α β γ - totalWelfare a b c (n : ℝ) 2 α β γ =
      β * (64 * α ^ 6 + 64 * α ^ 5 * (3 * β + 4 * (n : ℝ) * γ) +
        (1 + (n : ℝ)) * γ ^ 3 * (β + γ) * (4 * (-3 + (n : ℝ)) * β ^ 2 +
          4 * (-5 + 3 * (n : ℝ)) * β * γ + (-5 + 7 * (n : ℝ)) * γ ^ 2) +
        16 * α ^ 4 * (12 * β ^ 2 + (-1 + 33 * (n : ℝ)) * β * γ +
          (-15 + 34 * (n : ℝ) + 7 * (n : ℝ) ^ 2) * γ ^ 2) +
        4 * α * γ ^ 2 * (4 * (-4 + (n : ℝ)) * β ^ 3 +
          2 * (-25 + 4 * (n : ℝ) + 7 * (n : ℝ) ^ 2) * β ^ 2 * γ +
          (-47 + 11 * (n : ℝ) + 29 * (n : ℝ) ^ 2) * β * γ ^ 2 +
          2 * (-6 + 4 * (n : ℝ) + 7 * (n : ℝ) ^ 2) * γ ^ 3) +
        32 * α ^ 3 * (2 * β ^ 3 + (-1 + 9 * (n : ℝ)) * β ^ 2 * γ +
          (-16 + 25 * (n : ℝ) + 5 * (n : ℝ) ^ 2) * β * γ ^ 2 +
          (-10 + 14 * (n : ℝ) + 7 * (n : ℝ) ^ 2) * γ ^ 3) +
        4 * α ^ 2 * γ * (4 * (-1 + (n : ℝ)) * β ^ 3 +
          4 * (-21 + 17 * (n : ℝ) + 3 * (n : ℝ) ^ 2) * β ^ 2 * γ +
          (-126 + 95 * (n : ℝ) + 59 * (n : ℝ) ^ 2) * β * γ ^ 2 +
          (-45 + 44 * (n : ℝ) + 42 * (n : ℝ) ^ 2) * γ ^ 3)) /
      (b * (Psi (n : ℝ) 1 α β γ / 2) ^ 2 * Psi (n : ℝ) 2 α β γ ^ 2) ∧
    totalWelfare a b c (n : ℝ) 2 α β γ < totalWelfare a b c (n : ℝ) 1 α β γ := by sorry

end FarmerInfoProvision
