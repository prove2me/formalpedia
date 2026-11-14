-- Prove2me | Theorems.Thm_BosonicLearn_husimi_fourier
-- name    : BosonicLearn.husimi_fourier
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:22:45.07608+00:00
-- url     : https://prove2.me/theorems/da9f1633-cfe8-4acf-bbc7-baab799033dc
-- title:
--   Fourier transform of the Husimi function: $\int e^{it\cdot\beta}Q_\rho(\beta)\,d\beta=e^{-|t|^2/4}\,\mathrm{Tr}(\rho\,e^{it\cdot\hat r})$ for every state $\rho$
-- statement:
--   The Husimi function of a state and its Weyl characteristic function.
--
--   Let $\rho$ be a state (density operator) on the $n$-mode Fock space, $Q_\rho(\beta)=(2\pi)^{-n}\langle\alpha(\beta)|\rho|\alpha(\beta)\rangle$ its Husimi function in heterodyne coordinates $\beta\in\mathbb R^{2n}$, and $\chi_\rho(\xi)=\operatorname{Tr}(\rho\,e^{i\xi\cdot\hat r})$ its characteristic function. Then:
--
--   1. the iterated series defining $\chi_\rho(\xi)$ converge, for every $\xi$;
--   2. $Q_\rho\ge0$, and $Q_\rho$ is measurable and integrable on $\mathbb R^{2n}$;
--   3. for every $t\in\mathbb R^{2n}$,
--
--   $$
--   \int_{\mathbb R^{2n}}e^{it\cdot\beta}\,Q_\rho(\beta)\,d\beta=e^{-|t|^2/4}\,\chi_\rho(t).
--   $$
--
--   Role. At $t=0$: the heterodyne outcome law has total mass one. For a Gaussian state the right-hand side is $\exp(it\cdot\mu-\tfrac12t^T(\Sigma+\tfrac12)t)$, which is Eq. (207) of the paper (`BosonicLearn.eq_207`).
--
--   **Formalization Note** $Q_\rho$ is `husimiQ ρ.coefficients`, $\chi_\rho$ is the published `Support50.P14.oscillatorCharacteristic` at the interleaved copy of $t$, and the convergence statement is `OscillatorCharacteristicSummable`. The statement holds for every `State`, not only Gaussian ones.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5 (heterodyne measurement: the outcome distribution on ρ(µ, Σ) is N(µ, Σ + ½I)); proof of Theorem 8, Eq. (207), p. 61

import Mathlib
import Definitions.Def_BosonicLearn_husimiQ
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (oscillatorCharacteristic OscillatorCharacteristicSummable)
open MeasureTheory

namespace BosonicLearn

/-- **Fourier transform of the Husimi function: `∫ e^{it·β} Q_ρ(β) dβ = e^{−|t|²/4} Tr(ρ e^{it·r̂})`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5: "heterodyne measurement, whose outcome distribution on an n-mode Gaussian state ρ(µ, Σ) is a 2n-variate classical
Gaussian N(µ, Σ + ½I)", and Eq. (207), p. 61.

For every state `ρ` on the `n`-mode Fock space: the Weyl characteristic function `χ_ρ(ξ) = Tr(ρ e^{iξ·r̂})` is
given by convergent iterated series; the Husimi function `Q_ρ(β) = (2π)^{−n}⟨α(β)|ρ|α(β)⟩` is non-negative, measurable
and integrable on `ℝ²ⁿ`; and for all `t ∈ ℝ²ⁿ`

`∫ e^{it·β} Q_ρ(β) dβ = e^{−|t|²/4} χ_ρ(t)`.

**Formalization Note.** `Q_ρ` is `husimiQ ρ.coefficients`, `χ_ρ` is the published
`Support50.P14.oscillatorCharacteristic` at the interleaved copy of `t` (`(j, 0) ↦ t_{q,j}`, `(j, 1) ↦ t_{p,j}`), and the
convergence statement is `OscillatorCharacteristicSummable`. At `t = 0` the identity says that the heterodyne
outcome law has total mass one. -/
theorem husimi_fourier {n : ℕ} (ρ : State (Occupation (Fin n))) :
    OscillatorCharacteristicSummable ρ.coefficients ∧
    (∀ β : Fin n ⊕ Fin n → ℝ, 0 ≤ husimiQ ρ.coefficients β) ∧
    Measurable (husimiQ ρ.coefficients) ∧
    Integrable (husimiQ ρ.coefficients) ∧
    ∀ t : Fin n ⊕ Fin n → ℝ,
      ∫ β : Fin n ⊕ Fin n → ℝ, Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ)) *
          ((husimiQ ρ.coefficients β : ℝ) : ℂ) =
        ((Real.exp (-(∑ a, t a ^ 2) / 4) : ℝ) : ℂ) *
          oscillatorCharacteristic ρ.coefficients
            (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) := by sorry

end BosonicLearn
