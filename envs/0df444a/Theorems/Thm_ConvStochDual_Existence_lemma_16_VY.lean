-- Prove2me | Theorems.Thm_ConvStochDual_Existence_lemma_16_VY
-- name    : ConvStochDual.Existence.lemma_16_VY
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T03:36:47.654961+00:00
-- url     : https://prove2.me/theorems/94565f0c-fb81-49b9-a67b-c3c7fc23d331
-- title:
--   Lemma 16 on $\mathcal V\times\mathcal Y$ — $\varphi^*(p,y)=Ef^*(p,y)$ for $p\in\mathcal X_a^\perp$, $y\in\mathcal Y$
-- statement:
--   In the setting of Pennanen–Perkkiö, consider the value function of $(SP_{\mathcal X})$,
--
--   $$\varphi(z,u)=\inf_{x\in\mathcal X}\{Ef(x,u)\mid x-z\in\mathcal N\},\qquad (z,u)\in\mathcal X\times\mathcal U,$$
--
--   where $\mathcal N$ is the space of adapted strategies and $Ef(x,u)=\mathbb E[f(x(\omega),u(\omega),\omega)]$ for a convex normal integrand $f$. Its conjugate with respect to the pairing of $\mathcal X\times\mathcal U$ with $\mathcal V\times\mathcal Y$ is
--
--   $$\varphi^*(p,y)=\sup_{z\in\mathcal X,\,u\in\mathcal U}\big\{\langle z,p\rangle+\langle u,y\rangle-\varphi(z,u)\big\}.$$
--
--   Assume the standing assumptions (in particular, all spaces are decomposable) and that $\operatorname{dom}Ef\cap(\mathcal X\times\mathcal U)\neq\emptyset$. Then for every $p\in\mathcal X_a^\perp$ and $y\in\mathcal Y$,
--
--   $$\varphi^*(p,y)=Ef^*(p,y)=\mathbb E\big[f^*(p(\omega),y(\omega),\omega)\big],$$
--
--   where $f^*(\cdot,\cdot,\omega)$ is the scenario-wise convex conjugate of $f(\cdot,\cdot,\omega)$.
--
--   This is the case $(p,y)\in\mathcal V\times\mathcal Y$ of Lemma 16 of the source: there $p^s=0$ and $y^s=0$, so the support-function term vanishes, and $p\in\mathcal X_a^\perp$ makes the indicator term vanish. Equivalently, it is the formula $F^*(0,p,y)=Ef^*(p,y)+\delta_{\mathcal X_a^\perp}(p)$ stated on p. 3 of the source, citing Lemma 13 of the companion paper (arXiv:2205.02045). It identifies the ordinary dual objective $\langle\bar u,y\rangle-Ef^*(p,y)$ with the strong dual objective at the pair of continuous functionals $(\langle\cdot,p\rangle,\langle\cdot,y\rangle)$.
--
--   **Formalization Note** The conjugate $Ef^*$ of the integral functional is written directly as the integral functional of the pointwise conjugate (`EfStar`), as in the source's notation. The integral convention is the paper's: $+\infty$ unless the positive part is integrable.
-- source:
--   Pennanen & Perkkiö, Dual solutions in convex stochastic optimization, arXiv:2205.15825v1, p. 14, Lemma 16 (case (p,y) ∈ V × Y), equivalently p. 3 display F*(v,p,y) = Ef*(v+p,y) + δ_{X_a^⊥}(p) citing [13, Lemma 13] (arXiv:2205.02045v1)

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

/-- Pennanen–Perkkiö, arXiv:2205.15825v1, p. 14, Lemma 16 restricted to
`(p, y) ∈ V × Y` (equivalently p. 3, `F*(0,p,y) = Ef*(p,y) + δ_{X_a^⊥}(p)`, via [13, Lemma 13]):
for `p ∈ X_a^⊥` and `y ∈ Y`, the conjugate of the value function equals the integral
of the scenario-wise conjugate. -/
theorem lemma_16_VY (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (hdom : ∃ q : X × U, Ef s (ιX q.1) (ιU q.2) < ⊤)
    (p : V) (hp : p ∈ XaPerp s) (y : Y) :
    phiStarV s p y = EfStar s (p : RV Ω P n) (y : RV Ω P m) := by sorry

end ConvStochDual.Existence
