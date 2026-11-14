-- Prove2me | Theorems.Thm_BosonicLearn_thermal_displaced_kernel
-- name    : BosonicLearn.thermal_displaced_kernel
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:32:09.987812+00:00
-- url     : https://prove2.me/theorems/39fe1e0f-c76a-4a80-bfe3-f324fdbfe5c3
-- title:
--   The $\chi^2$-kernel of displaced thermal states: $\mathrm{Tr}[\tau_z\tau^{-1/2}\tau_{z'}\tau^{-1/2}]=\exp(2\kappa\,\mathrm{Re}\langle z,z'\rangle)$, $\kappa=(1-r)/\sqrt r$
-- statement:
--   Displaced thermal states are "coherent vectors" for the inner product $\langle X,Y\rangle_\tau=\operatorname{Tr}[X\tau^{-1/2}Y\tau^{-1/2}]$. This identity is the key computation in a proof of the one-sided relative covariance bound (Theorem 7) through a $\chi^2$-divergence relative to a thermal state.
--
--   Let $\tau=((1-r)\,r^{a^\dagger a})^{\otimes n}$ with $0<r<1$, Fock weights $p_w=(1-r)^nr^{|w|}$, and $\tau_z=D(z)\tau D(z)^\dagger$ for $z\in\mathbb C^n$, i.e. $(\tau_z)_{uv}=\sum_wD(z)_{uw}\,p_w\,\overline{D(z)_{vw}}$. Then for all $z,z'\in\mathbb C^n$
--
--   $$\sum_{u,v}\frac{(\tau_z)_{uv}\,\overline{(\tau_{z'})_{uv}}}{\sqrt{p_up_v}}=\exp\Big(\kappa\sum_j(\bar z_jz'_j+z_j\bar z'_j)\Big),\qquad\kappa=\frac{1-r}{\sqrt r},$$
--
--   and the double series converges absolutely. For $r=\nu/(1+\nu)$ (covariance $(\frac12+\nu)I$), $\kappa=1/\sqrt{\nu(1+\nu)}$.
--
--   Proof idea: with $W(x,y)=e^{xa^\dagger}e^{ya}$ one has $W(x,y)W(x',y')=e^{yx'}W(x+x',y+y')$, $D(z)=e^{-|z|^2/2}W(z,-\bar z)$, $r^{sN}W(x,y)r^{-sN}=W(r^sx,r^{-s}y)$ and $\operatorname{Tr}[r^NW(x,y)]=(1-r)^{-1}e^{rxy/(1-r)}$. Checked numerically (error $<10^{-11}$).
--
--   **Formalization Note** $\langle m|D(z)|k\rangle$ is the published `displacementMatrix z m k`; the weights and the arrays $\tau_z$ are introduced by equations; the first conclusion is the absolute convergence of the series defining $(\tau_z)_{uv}$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §7.1, Theorem 7, Eqs. (184)–(185), p. 55

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace BosonicLearn

/-- **The `χ²`-kernel of displaced thermal states: `Tr[τ_z τ^{−1/2} τ_{z′} τ^{−1/2}] = exp(2κ Re⟨z, z′⟩)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.1, Theorem 7, Eqs. (184)–(185), p. 55 (one-sided relative covariance bound); this identity is the key
computation of a proof of that bound through a `χ²`-divergence relative to a thermal state.

Let `τ = ((1 − r) r^{a†a})^{⊗n}`, `0 < r < 1`, with Fock weights `p_w = (1 − r)ⁿ r^{|w|}`, and
`τ_z = D(z) τ D(z)†` the displaced thermal state, `(τ_z)_{uv} = ∑_w D(z)_{uw} p_w \overline{D(z)_{vw}}`
(`D(z)_{uw} = ∏ⱼ ⟨u_j|D(z_j)|w_j⟩`). Then, with `κ = (1 − r)/√r`,

`∑_{u,v} (τ_z)_{uv} \overline{(τ_{z′})_{uv}} / √(p_u p_v) = exp(κ ∑ⱼ (z̄ⱼ z′ⱼ + zⱼ z̄′ⱼ))`,

and the double series converges absolutely.

**Formalization Note.** `⟨m|D(z)|k⟩` is the published `displacementMatrix z m k`. The weights and the arrays `τ_z`
are introduced by equations. The first conclusion is the absolute convergence of the series defining `(τ_z)_{uv}`.
For `r = ν/(1 + ν)` (covariance `(½ + ν)I`), `κ = 1/√(ν(1 + ν))`. -/
theorem thermal_displaced_kernel {n : ℕ} (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z z' : Fin n → ℂ)
    (p : (Fin n → ℕ) → ℝ) (hp : p = fun w => (1 - r) ^ n * r ^ (∑ i, w i))
    (T : (Fin n → ℂ) → (Fin n → ℕ) → (Fin n → ℕ) → ℂ)
    (hT : T = fun z u v => ∑' w : Fin n → ℕ,
      (∏ j, displacementMatrix (z j) (u j) (w j)) * ((p w : ℝ) : ℂ) *
        star (∏ j, displacementMatrix (z j) (v j) (w j))) :
    (∀ (y : Fin n → ℂ) (u v : Fin n → ℕ), Summable fun w : Fin n → ℕ =>
      ‖(∏ j, displacementMatrix (y j) (u j) (w j)) * ((p w : ℝ) : ℂ) *
        star (∏ j, displacementMatrix (y j) (v j) (w j))‖) ∧
    Summable (fun x : (Fin n → ℕ) × (Fin n → ℕ) =>
      ‖T z x.1 x.2‖ * ‖T z' x.1 x.2‖ / Real.sqrt (p x.1 * p x.2)) ∧
    HasSum (fun x : (Fin n → ℕ) × (Fin n → ℕ) =>
      T z x.1 x.2 * star (T z' x.1 x.2) / ((Real.sqrt (p x.1 * p x.2) : ℝ) : ℂ))
      (Complex.exp ((((1 - r) / Real.sqrt r : ℝ) : ℂ) *
        ∑ j, (star (z j) * z' j + z j * star (z' j)))) := by sorry

end BosonicLearn
