-- Prove2me | Theorems.Thm_FarmerInfoProvision_proposition_2_proof_omega_signs
-- name    : FarmerInfoProvision.proposition_2_proof_omega_signs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:46:30.579749+00:00
-- url     : https://prove2.me/theorems/964c0770-4c29-43f3-9e80-912be0281403
-- title:
--   Proof of Proposition 2: $\Omega_d>0$ and $\Omega_n$ is affine and strictly decreasing in $n_1$
-- statement:
--   For $n\ge4$, $b,\alpha,\beta>0$ and $\gamma\ge0$:
--
--   1. $\Omega_d(n_1,\beta;\gamma)>0$ for every real $n_1>0$;
--   2. $\Omega_n(n_1,\beta;\gamma)$ is linearly decreasing in $n_1$: there are constants $k_0$ and $k_1<0$ with
--   $$
--   \Omega_n(n_1,\beta;\gamma)=k_0+k_1n_1\quad\text{for every real } n_1.
--   $$
--
--   Together with the derivative formula this shows that the welfare, as a function of a continuous $n_1$, increases and then decreases.
--
--   Differences from the source:
--   - encoding: Ω_n is linearly decreasing in n1 → Ω_n(n1) = k₀ + k₁·n1 for all real n1, with k₁ < 0; reason: the standard meaning of an affine function that is strictly decreasing
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, p. 35

import Mathlib
import Definitions.Def_FarmerInfoProvision_OmegaN
import Definitions.Def_FarmerInfoProvision_OmegaD

namespace FarmerInfoProvision

/-- **Proof of Proposition 2: `Ω_d > 0` and `Ω_n` is affine and strictly decreasing in `n1`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, p. 35: "In this case,
`Ω_d(n1, β; γ)` is strictly positive and `Ω_n(n1, β; γ)` is linearly decreasing in `n1`."

For `n ≥ 4` farmers, `b, α, β > 0` and `γ ≥ 0`:
1. `Ω_d(t, β; γ) > 0` for every real `t > 0`;
2. there are reals `k₀` and `k₁ < 0` with `Ω_n(t, β; γ) = k₀ + k₁ t` for every real `t`.

**Formalization Note.** "Linearly decreasing" is read as affine with negative slope. `n1 > 0`
is the proof's standing case ("we first assume that `n1 > 0`", p. 35). -/
theorem proposition_2_proof_omega_signs {n : ℕ} (hn : 4 ≤ n) {b α β γ : ℝ}
    (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    (∀ t : ℝ, 0 < t → 0 < OmegaD b (n : ℝ) t α β γ) ∧
    ∃ k₀ k₁ : ℝ, k₁ < 0 ∧ ∀ t : ℝ, OmegaN (n : ℝ) t α β γ = k₀ + k₁ * t := by sorry

end FarmerInfoProvision
