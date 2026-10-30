-- Prove2me | Theorems.Thm_FarmerInfoProvision_proposition_2_proof_welfare_derivative
-- name    : FarmerInfoProvision.proposition_2_proof_welfare_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:45:57.01714+00:00
-- url     : https://prove2.me/theorems/261a5c1e-82ce-4a9b-9b68-c52a6af534f9
-- title:
--   Proof of Proposition 2: the derivative of total welfare in $n_1$ is $\Omega_n/\Omega_d$
-- statement:
--   Let $W(n_1,\beta;\gamma)=n_1W^I(n_1,\beta;\gamma)+(n-n_1)W^J(n_1,\beta;\gamma)$ be the total welfare built from Lemma 2's closed forms, with $n_1$ treated as a continuous variable. For $n\ge4$, $a,b,\alpha,\beta>0$, $\gamma\ge0$ and every real $n_1>0$,
--
--   $$
--   \frac{\partial}{\partial n_1}W(n_1,\beta;\gamma)=\frac{\Omega_n(n_1,\beta;\gamma)}{\Omega_d(n_1,\beta;\gamma)},
--   $$
--
--   with $\Omega_n$ and $\Omega_d$ the explicit expressions printed in the proof.
--
--   This is the first step of the proof of Proposition 2: the sign of the derivative is the sign of $\Omega_n$.
--
--   Differences from the source:
--   - encoding: the closed forms contain 1/γ, undefined at γ = 0 → Lean's 1/0 = 0, multiplied by A1² = B1² = 0; reason: at γ = 0 the formulas take their γ → 0 limits, so γ = 0 (no private signal) is covered with its intended values
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 35

import Mathlib
import Definitions.Def_FarmerInfoProvision_totalWelfare
import Definitions.Def_FarmerInfoProvision_OmegaN
import Definitions.Def_FarmerInfoProvision_OmegaD

namespace FarmerInfoProvision

/-- **Proof of Proposition 2: the derivative of total welfare in `n1` is `Ω_n/Ω_d`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 35:
"we first assume that `n1 > 0` and it takes continuous values and evaluate its corresponding
derivative: `∂/∂n1 W(n1, β; γ) = Ω_n(n1, β; γ)/Ω_d(n1, β; γ)`, where `Ω_n(n1, β; γ)` and
`Ω_d(n1, β; γ)` can be expressed explicitly".

For `n ≥ 4` farmers, `a, b, α, β > 0`, `γ ≥ 0` and every real `t > 0`, the function
`s ↦ W(s, β; γ) = totalWelfare a b c n s α β γ` has derivative
`OmegaN n t α β γ / OmegaD b n t α β γ` at `t`.

**Formalization Note.** `W` is Lemma 2's closed form `n1 W^I + (n − n1) W^J` with `n1` real. At
`γ = 0` its `1/γ` terms are junk values multiplied by `0`, and `W` is then the `γ → 0` limit of
the formula, to which the derivative formula applies as well. -/
theorem proposition_2_proof_welfare_derivative {n : ℕ} (hn : 4 ≤ n) {a b c α β γ t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) (ht : 0 < t) :
    HasDerivAt (fun s => totalWelfare a b c (n : ℝ) s α β γ)
      (OmegaN (n : ℝ) t α β γ / OmegaD b (n : ℝ) t α β γ) t := by sorry

end FarmerInfoProvision
