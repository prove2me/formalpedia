-- Prove2me | Theorems.Thm_BosonicLearn_fugacity_renyi2_tensorPow
-- name    : BosonicLearn.fugacity_renyi2_tensorPow
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:10:24.000723+00:00
-- url     : https://prove2.me/theorems/401bbdee-996a-47cb-9f08-44166b38725e
-- title:
--   Rényi-2 overlap of $\rho_R^{\otimes N}$ with a thermal state: $\big(\det(1-R)^2/((1-r_0)^n\det(1-R^2/r_0))\big)^N$
-- statement:
--   A closed form for $\operatorname{Tr}(\rho\,\sigma^{-1/2}\rho\,\sigma^{-1/2})$ when $\rho$ is $N$ copies of a passive Gaussian state and $\sigma$ is $N$ copies of a thermal state.
--
--   Let $R$ be a fugacity matrix ($0\preceq R\prec\mathbf 1$) with $R^2\prec r_0\mathbf 1$, $0<r_0<1$, let $\rho_R=\det(\mathbf 1-R)\Gamma(R)$ and $p_0(u)=(1-r_0)^nr_0^{|u|}$ (the diagonal of the thermal state of fugacity $r_0$). Then $\rho_R^{\otimes N}$ is a density operator, the weights $\prod_tp_0(x_t)$ on $(\mathbb N^n)^N$ are positive with sum $1$, $\det(\mathbf 1-R^2/r_0)>0$, and
--
--   $$\sum_{x,y}\frac{\big|(\rho_R^{\otimes N})_{xy}\big|^2}{\sqrt{\prod_tp_0(x_t)\prod_tp_0(y_t)}}=\Big(\frac{\det(\mathbf 1-R)^2}{(1-r_0)^n\,\det(\mathbf 1-R^2/r_0)}\Big)^N .$$
--
--   Proof idea: $\Gamma(R)$ is block diagonal in the photon number, $\Gamma(cR)_{uv}=c^{|u|}\Gamma(R)_{uv}$, $\Gamma$ is multiplicative and $\operatorname{Tr}\Gamma(A)=1/\det(\mathbf 1-A)$; sums over $N$ copies factorize.
--
--   **Formalization Note** `fugacityCoeff R` is $\rho_R$; the tensor power is `WildeQIT.Schumacher.tensorPow`. Real parts of the (positive real) determinants are used.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §8, proof of Theorem 9, pp. 65–67 (Eqs. (230)–(234): the divergence of the ensemble $\{\rho_{U_a}^{\otimes N}\}$ is bounded through single copies)

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_WildeQIT_Schumacher_tensorPow

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn

/-- **Rényi-2 overlap of `N` copies of a passive Gaussian state with a thermal reference state.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §8, proof of Theorem 9, Eqs. (230)–(234), pp. 66–67 (the Holevo quantity of the ensemble `{ρ_{U_a}^{⊗N}}` is bounded
through the pairwise divergences of single copies); here the divergence is the Rényi-2 quantity
`Tr(ρ σ^{−1/2} ρ σ^{−1/2})` relative to the thermal state `σ = (1 − r₀)ⁿ Γ(r₀·1)`.

Let `R` be a fugacity matrix (`0 ⪯ R ≺ 1`) with `R² ≺ r₀·1`, `0 < r₀ < 1`, and let `p₀(u) = (1 − r₀)ⁿ r₀^{|u|}` be the
diagonal of the thermal state. Then `ρ_R^{⊗N}` is a density operator, the weights `∏ₜ p₀(x_t)` on `(ℕⁿ)^N` are positive
with sum `1`, and

`∑_{x,y} |(ρ_R^{⊗N})_{xy}|² / √(∏ₜ p₀(x_t) ∏ₜ p₀(y_t)) = ( det(1 − R)² / ((1 − r₀)ⁿ det(1 − R²/r₀)) )^N`.

**Formalization Note.** `ρ_R = det(1 − R)Γ(R)` is `fugacityCoeff R`; `ρ^{⊗N}` is `WildeQIT.Schumacher.tensorPow`. For one
copy, `Γ(R)` is block diagonal in the photon number, `Γ(r₀^{−1/2}R)_{uv} = r₀^{−|u|/2}Γ(R)_{uv}`, `Γ` is multiplicative and
`Tr Γ(A) = 1/det(1 − A)`. Both determinants are positive reals; their real parts are used. -/
theorem fugacity_renyi2_tensorPow {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) (r₀ : ℝ) (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hR2 : (((r₀ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R * R).PosDef) (N : ℕ) :
    IsDensity (WildeQIT.Schumacher.tensorPow N (fugacityCoeff R)) ∧
    HasSum (fun x : Fin N → Occupation (Fin n) => ∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x t i))) 1 ∧
    0 < (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det.re ∧
    HasSum (fun x : (Fin N → Occupation (Fin n)) × (Fin N → Occupation (Fin n)) =>
        ‖WildeQIT.Schumacher.tensorPow N (fugacityCoeff R) x.1 x.2‖ ^ 2 /
          Real.sqrt ((∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x.1 t i))) *
            ∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x.2 t i))))
      (((1 - R).det.re ^ 2 /
        ((1 - r₀) ^ n * (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det.re)) ^ N) := by sorry

end BosonicLearn
