-- Prove2me | Theorems.Thm_BosonicLearn_classical_displacement_bound
-- name    : BosonicLearn.classical_displacement_bound
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T21:34:15.87317+00:00
-- url     : https://prove2.me/theorems/39a73d62-b4d2-4d02-a201-e8008fee158c
-- title:
--   Displacing a classical state by $d$ moves it by at most $|d|/\sqrt2$ in trace distance
-- statement:
--   A displacement bound for classical states.
--
--   Let $\sigma$ be a classical state on the $n$-mode Fock space: a mixture $\int|\alpha(x)\rangle\langle\alpha(x)|\,d\gamma(x)$ of coherent states over a probability measure $\gamma$ on phase space, specified through $\chi_\sigma(\xi)=\hat\gamma(\xi)\,e^{-|\xi|^2/4}$. Let $\sigma'$ be the state displaced by $d\in\mathbb R^{2n}$, i.e. $\chi_{\sigma'}(\xi)=e^{i\xi\cdot d}\chi_\sigma(\xi)$. Then
--
--   $$
--   \tfrac12\|\sigma'-\sigma\|_1\ \le\ \frac{|d|}{\sqrt2}.
--   $$
--
--   Reason: $\tfrac12\||\alpha\rangle\langle\alpha|-|0\rangle\langle0|\|_1=\sqrt{1-e^{-|\alpha|^2}}\le|\alpha|$ with $|\alpha|^2=|d|^2/2$, and the mixture does not increase the distance. The bound fails for non-classical (for example strongly squeezed) states.
--
--   Role. Used in `BosonicLearn.lemma_18_classical` for the part of a mean shift that is not absorbed in the mixing measure.
--
--   **Formalization Note** $\gamma$ is a probability measure on `EuclideanSpace ℝ (Fin n × Fin 2)`, $\hat\gamma$ is `charFun`, $\xi\cdot d$ is `meanForm d ξ`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 18 (first-moment perturbation), Eq. (204), p. 60; §1.1, p. 5 (coherent states)

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Displacing a classical state by `d` moves it by at most `|d|/√2` in trace distance.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 18 (first-moment perturbation), Eq. (204), p. 60; §1.1, p. 5 (coherent states).

Let `σ` be a classical state on the `n`-mode Fock space: a mixture `∫ |α(x)⟩⟨α(x)| dγ(x)` of coherent states over a
probability measure `γ` on phase space, specified through its characteristic function
`χ_σ(ξ) = γ̂(ξ) e^{−|ξ|²/4}`. If `σ'` is the state displaced by `d ∈ ℝ²ⁿ`, `χ_{σ'}(ξ) = e^{iξ·d} χ_σ(ξ)`, then
`½‖σ' − σ‖₁ ≤ |d|/√2`.

**Formalization Note.** `γ` is a probability measure on `EuclideanSpace ℝ (Fin n × Fin 2)` (interleaved quadrature
coordinates) and `γ̂` is Mathlib's `charFun`. The bound comes from `½‖|α⟩⟨α| − |0⟩⟨0|‖₁ = √(1 − e^{−|α|²}) ≤ |α|` with
`|α|² = |d|²/2`, and does not hold for non-classical (e.g. squeezed) states. -/
theorem classical_displacement_bound {n : ℕ} (γ : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    [IsProbabilityMeasure γ] (σ σ' : State (Occupation (Fin n))) (d : Fin n × Fin 2 → ℝ)
    (hσ : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic σ.coefficients ξ =
      charFun γ (WithLp.toLp 2 ξ) * ((Real.exp (-(∑ a, ξ a ^ 2) / 4) : ℝ) : ℂ))
    (hσ' : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic σ'.coefficients ξ =
      Complex.exp (Complex.I * (meanForm d ξ : ℂ)) * oscillatorCharacteristic σ.coefficients ξ) :
    traceDist σ'.coefficients σ.coefficients ≤
      ENNReal.ofReal (Real.sqrt (∑ a, d a ^ 2) / Real.sqrt 2) := by sorry

end BosonicLearn
