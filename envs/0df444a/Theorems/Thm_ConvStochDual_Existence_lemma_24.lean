-- Prove2me | Theorems.Thm_ConvStochDual_Existence_lemma_24
-- name    : ConvStochDual.Existence.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:58.776879+00:00
-- url     : https://prove2.me/theorems/31450be0-2c3e-4537-9a0b-089ebf8db36a
-- title:
--   Lemma 24, p. 18 — conditional expectation improves the support bound
-- statement:
--   Under Assumption 23, fix a time $t$ and strong dual functionals $(p,y)$ with no $p$ component after time $t$. The conditional expectation $E_t$ acts on $\mathcal X$ and has a strong adjoint $E_t^*$. There is $\hat y\in\mathcal U^*$ such that
--
--   $$\sigma_{\operatorname{dom}Ef}(E_t^*p,\hat y)-\langle\bar u,\hat y\rangle\le \sigma_{\operatorname{dom}Ef}(p,y)-\langle\bar u,y\rangle.$$
--
--   This step moves a dual functional through one stage of the filtration without worsening its support value.
--
--   **Formalization Note** The statement also assumes $Ef$ proper and strongly lower semicontinuous, as needed by the conjugate theorem used on page 19. The continuous map supplied as $E_t$ is constrained to have the conditional-expectation action on every coordinate.
-- source:
--   Pennanen & Perkkiö, Dual solutions in convex stochastic optimization, arXiv:2205.15825v1, p. 18, Lemma 24; p. 19 proof

import Mathlib
import Definitions.Def_ConvStochDual_Existence_Setting

open MeasureTheory

namespace ConvStochDual.Existence

variable {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}

/-- Pennanen–Perkkiö, arXiv:2205.15825v1, p. 18, Lemma 24. -/
theorem lemma_24 (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (hEf : EfProperLsc s) (hEt : CondExpClosed s)
    (hA23 : Assumption23_1 s ∧ Assumption23_2 s)
    (t : Fin (T + 1)) (Et : X →L[ℝ] X)
    (hEt_repr : ∀ x : X, IsCondExpT s t x (Et x))
    (p : X →L[ℝ] ℝ) (y : U →L[ℝ] ℝ)
    (hp : HasPastSupport s t p) :
    ∃ yhat : U →L[ℝ] ℝ,
      sigmaDomEf s (p.comp Et) yhat - ((yhat s.ubar : ℝ) : EReal) ≤
        sigmaDomEf s p y - ((y s.ubar : ℝ) : EReal) := by sorry

end ConvStochDual.Existence
