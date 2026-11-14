-- Prove2me | Theorems.Thm_BosonicLearn_coherent_weyl_integral
-- name    : BosonicLearn.coherent_weyl_integral
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:17:07.840321+00:00
-- url     : https://prove2.me/theorems/8e11b066-7a20-44a4-8c0b-bec00a931377
-- title:
--   Fourier transform of coherent-state projectors: $\int e^{it\cdot\beta}|\alpha(\beta)\rangle\langle\alpha(\beta)|\,d\beta=(2\pi)^ne^{-|t|^2/4}e^{it\cdot\hat r}$ (matrix elements)
-- statement:
--   The Fourier transform of the coherent-state projectors, in Fock matrix elements.
--
--   For $\beta=(\beta_q,\beta_p)\in\mathbb R^{2n}$ let $|\alpha(\beta)\rangle$ be the $n$-mode coherent state with $\alpha_j=(\beta_{q,j}+i\beta_{p,j})/\sqrt2$, and $c(\beta)_u=\langle u|\alpha(\beta)\rangle$ its Fock coefficients. For all $t\in\mathbb R^{2n}$ and occupation vectors $u,v$,
--
--   $$
--   \int_{\mathbb R^{2n}}e^{it\cdot\beta}\,c(\beta)_v\,\overline{c(\beta)_u}\;d\beta=(2\pi)^n\,e^{-|t|^2/4}\,\langle v|e^{it\cdot\hat r}|u\rangle ,
--   $$
--
--   and the integrand is integrable.
--
--   Remarks. At $t=0$ this is the resolution of the identity by coherent states, $\int|\alpha(\beta)\rangle\langle\alpha(\beta)|\,d\beta/(2\pi)^n=\mathbf 1$. In general it is the anti-normally ordered form of the Weyl operator, and it gives the Fourier transform of the Husimi function (`BosonicLearn.husimi_fourier`). The single-mode identity was checked numerically.
--
--   **Formalization Note** $c(\beta)$ is `coherentVector β`; $\langle v|e^{it\cdot\hat r}|u\rangle$ is the published Weyl kernel `Support50.P14.oscillatorWeylKernel` at the interleaved copy of $t$ ($(j,0)\mapsto t_{q,j}$, $(j,1)\mapsto t_{p,j}$); the integral is over `Fin n ⊕ Fin n → ℝ` with the product Lebesgue measure.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5 (heterodyne measurement: the outcome distribution on ρ(µ, Σ) is N(µ, Σ + ½I)); proof of Theorem 8, Eq. (207), p. 61

import Mathlib
import Definitions.Def_BosonicLearn_coherentVector
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (oscillatorWeylKernel)
open MeasureTheory

namespace BosonicLearn

/-- **Fourier transform of coherent-state matrix elements: `∫ e^{it·β} |α(β)⟩⟨α(β)| dβ/(2π)ⁿ = e^{−|t|²/4} e^{it·r̂}`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5 (heterodyne measurement, the POVM `{π^{−n}|α⟩⟨α|}`, with outcome distribution `N(µ, Σ + ½I)` on `ρ(µ, Σ)`), and
Eq. (207), p. 61.

For `t ∈ ℝ²ⁿ` and occupation vectors `u, v`, with `c(β)` the Fock coefficients of the coherent vector `|α(β)⟩`,

`∫_{ℝ²ⁿ} e^{it·β} c(β)_v \overline{c(β)_u} dβ = (2π)ⁿ e^{−|t|²/4} ⟨v|e^{it·r̂}|u⟩`,

and the integrand is integrable.

**Formalization Note.** `c(β)` is `coherentVector β` (grouped coordinates `β = (β_q, β_p)`, `α_j = (β_{q,j} + iβ_{p,j})/√2`);
`⟨v|e^{it·r̂}|u⟩` is the published Weyl kernel `Support50.P14.oscillatorWeylKernel` at the interleaved copy of `t`
(`(j, 0) ↦ t_{q,j}`, `(j, 1) ↦ t_{p,j}`). At `t = 0` this is the resolution of the identity by coherent states. -/
theorem coherent_weyl_integral {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) (u v : Occupation (Fin n)) :
    Integrable (fun β : Fin n ⊕ Fin n → ℝ =>
      Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ)) * coherentVector β v *
        star (coherentVector β u)) ∧
    ∫ β : Fin n ⊕ Fin n → ℝ, Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ)) *
        coherentVector β v * star (coherentVector β u) =
      (((2 * Real.pi) ^ n * Real.exp (-(∑ a, t a ^ 2) / 4) : ℝ) : ℂ) *
        oscillatorWeylKernel
          (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) v u := by sorry

end BosonicLearn
