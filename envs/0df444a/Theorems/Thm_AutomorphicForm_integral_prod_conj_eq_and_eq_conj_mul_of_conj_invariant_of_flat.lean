-- Prove2me | Theorems.Thm_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
-- name    : AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/a0bbfa83-59c1-59e9-a58a-ba9dc681fbc0
-- title:
--   Two-sided average of a conjugation-invariant flat function
-- statement:
--   Let $F$ be a number field and write $\mathcal K = \prod_{w\mid\infty}$ `rowIsometrySubgroup₀ w.Completion` for the product, over the infinite places $w$ of $F$, of the groups `rowIsometrySubgroup₀ w.Completion` inside $GL_2(F_w)$, equipped with a Borel measurable structure. Let $\mu$ be a finite measure on $\mathcal K$ that is invariant under left translation, under right translation and under inversion, and let $\iota\colon\mathcal K\to GL_2(F_\infty)$ be a monoid homomorphism into the general linear group of the infinite adele ring whose $w$-th component, taken via `archComponent` (the map induced by evaluation $a\mapsto a_w$), is $\kappa\mapsto\kappa_w$ for every infinite place $w$. Let $\sigma\in\mathbb R$, let $e\colon\mathcal K\to\mathbb C$ satisfy $e(\kappa'\kappa\kappa'^{-1})=e(\kappa)$ for all $\kappa,\kappa'$ and $e(\kappa^{-1})=\overline{e(\kappa)}$, and let $h\colon GL_2(F_\infty)\to\mathbb C$ satisfy $h(j_w(k)\,x\,j_w(k)^{-1}) = h(x)$ for every infinite place $w$, every $k$ in `rowIsometrySubgroup₀ w.Completion` and every $x$, where $j_w =$ `archRowIsometryInclAt₀ F w`, and $$h(x)=\overline{h(x^{-1})}\cdot\bigl(\lVert\det(\mathrm{adelicArchGLIncl}\, F\,x)\rVert^{-\sigma}\bigr),$$ the norm being the idele norm of [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) (the value of the distributive Haar character of the adele ring of $F$), applied to the determinant of the image of $x$ under the embedding of $GL_2(F_\infty)$ into $GL_2(\mathbb A_F)$ with trivial finite component. Put $$\phi(x)=\int_{\mathcal K\times\mathcal K} e(\kappa_1)\,e(\kappa_2)\,h\bigl(\iota(\kappa_1)^{-1}x\,\iota(\kappa_2)^{-1}\bigr)\,d(\mu\otimes\mu).$$ The conclusion is the conjunction of two assertions: first, $\phi(j_w(k)\,x\,j_w(k)^{-1}) = \phi(x)$ for every infinite place $w$, every $k$ in `rowIsometrySubgroup₀ w.Completion` and every $x$; second, $\phi(x)=\overline{\phi(x^{-1})}\cdot\lVert\det(\mathrm{adelicArchGLIncl}\, F\,x)\rVert^{-\sigma}$ for every $x$. No measurability or integrability hypotheses on $e$ and $h$ are imposed, the integrals being Bochner integrals.
--
--   The statement says that the two-sided average of a function on $GL_2(F_\infty)$ against a class function on the product of the archimedean row-isometry groups inherits both the conjugation invariance at each infinite place and the functional equation $h(x)=\overline{h(x^{-1})}\lVert\det x\rVert^{-\sigma}$; it is the invariance bookkeeping needed when one replaces a test function by its bi-$\mathcal K$-average. It is used in the approximation arguments for cuspidal constituents, where such averaged functions serve as conjugation-invariant flat approximate identities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (σ : ℝ)
    (e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ)
    (hecl : ∀ κ κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e (κ' * κ * κ'⁻¹) = e κ)
    (hefl : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e κ⁻¹ = conj (e κ))
    (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hhc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      h (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = h x)
    (hhf : ∀ x : GL (Fin 2) (InfiniteAdeleRing F), h x = conj (h x⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ)) :
    (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
          e p.1 * e p.2 * h ((ι p.1)⁻¹ * (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) * (ι p.2)⁻¹)
          ∂(μ.prod μ)) =
      ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) ∂(μ.prod μ)) ∧
    ∀ x : GL (Fin 2) (InfiniteAdeleRing F),
      (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) ∂(μ.prod μ)) =
        conj (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x⁻¹ * (ι p.2)⁻¹) ∂(μ.prod μ)) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) := by sorry
