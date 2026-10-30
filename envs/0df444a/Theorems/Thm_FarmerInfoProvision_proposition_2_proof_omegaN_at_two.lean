-- Prove2me | Theorems.Thm_FarmerInfoProvision_proposition_2_proof_omegaN_at_two
-- name    : FarmerInfoProvision.proposition_2_proof_omegaN_at_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:08.737278+00:00
-- url     : https://prove2.me/theorems/6dfbc092-6a0a-4995-8834-f5cd72702355
-- title:
--   Proof of Proposition 2: $\Omega_n(2,\beta;\gamma)<0$
-- statement:
--   For $n\ge3$, $\alpha,\beta>0$ and $\gamma\ge0$,
--
--   $$
--   \begin{aligned}
--   \Omega_n(2,\beta;\gamma)=-4\beta\Bigl\{&16\alpha^4+8\alpha^3\bigl(4\beta+(1+4n)\gamma\bigr)+\gamma^2\bigl(2(-3+n)\beta^2+(-9+7n)\beta\gamma+2(-1+2n)\gamma^2\bigr)\\
--   &+4\alpha^2\bigl(4\beta^2+(3+8n)\beta\gamma+3(-1+4n)\gamma^2\bigr)+2\alpha\gamma\bigl(2\beta^2+(-10+15n)\beta\gamma+(-5+12n)\gamma^2\bigr)\Bigr\},
--   \end{aligned}
--   $$
--
--   and this number is negative.
--
--   Since $\Omega_n$ is decreasing in $n_1$, the welfare is strictly decreasing for $n_1\ge2$: informing more than two farmers is never optimal.
--
--   Differences from the source:
--   - generalization: standing assumption n ≥ 4 farmers (p. 8) → 3 ≤ n; reason: the sentence itself states the claim 'as long as n ≥ 3'; the statement specializes to every n ≥ 4
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 36

import Mathlib
import Definitions.Def_FarmerInfoProvision_OmegaN

namespace FarmerInfoProvision

/-- **Proof of Proposition 2: `Ω_n(2, β; γ) < 0`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 36:
"while evaluating `Ω_n(n1, β; γ)` at `n1 = 2`, `Ω_n(2, β; γ) = −4β{16α⁴ + 8α³(4β + (1 + 4n)γ)
+ γ²(2(−3 + n)β² + (−9 + 7n)βγ + 2(−1 + 2n)γ²) + 4α²(4β² + (3 + 8n)βγ + 3(−1 + 4n)γ²)
+ 2αγ(2β² + (−10 + 15n)βγ + (−5 + 12n)γ²)}`, which is necessarily negative (as long as
`n ≥ 3`)."

For `n ≥ 3` farmers, `α, β > 0` and `γ ≥ 0`, `Ω_n(2, β; γ)` equals the printed expression and
is negative.

**Formalization Note.** The hypothesis `n ≥ 3` is the one printed in this sentence; the
paper's standing assumption is `n ≥ 4`. -/
theorem proposition_2_proof_omegaN_at_two {n : ℕ} (hn : 3 ≤ n) {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    OmegaN (n : ℝ) 2 α β γ =
      -4 * β * (16 * α ^ 4 + 8 * α ^ 3 * (4 * β + (1 + 4 * (n : ℝ)) * γ) +
        γ ^ 2 * (2 * (-3 + (n : ℝ)) * β ^ 2 + (-9 + 7 * (n : ℝ)) * β * γ +
          2 * (-1 + 2 * (n : ℝ)) * γ ^ 2) +
        4 * α ^ 2 * (4 * β ^ 2 + (3 + 8 * (n : ℝ)) * β * γ + 3 * (-1 + 4 * (n : ℝ)) * γ ^ 2) +
        2 * α * γ * (2 * β ^ 2 + (-10 + 15 * (n : ℝ)) * β * γ +
          (-5 + 12 * (n : ℝ)) * γ ^ 2)) ∧
    OmegaN (n : ℝ) 2 α β γ < 0 := by sorry

end FarmerInfoProvision
