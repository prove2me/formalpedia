-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
-- name    : AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/b8acfb47-f212-5577-9826-a2b2ee10b7a9
-- title:
--   Sandwiched smoothing on reproduced vectors is archimedean smoothing
-- statement:
--   Let $F$ be a number field and put $\mathcal K=\prod_{w\mid\infty}$ `rowIsometrySubgroup₀ w.Completion`, the product over the infinite places of $F$ of the indicated subgroups of $GL_2(F_w)$, equipped with a measurable structure that is the Borel one. Let $\mu$ be a probability measure on $\mathcal K$ invariant under both left and right translation, and let $\iota:\mathcal K\to GL_2(\mathbb A_{F,\infty})$ be a continuous group homomorphism whose component at each infinite place $w$ (the image under `archComponent`, induced by evaluation of an infinite adele at $w$) is the inclusion of the $w$-th coordinate $\kappa_w$ into $GL_2(F_w)$. Let $GL_2(\mathbb A_{F,\infty})$ carry its Borel structure and let $\mu a$ be a Haar measure on it that is also right invariant. Let $U$ be a subgroup of $GL_2(\mathbb A_F)$ contained in the kernel of `glArch` (so every element of $U$ has trivial archimedean part), whose image under `glFin`, the reduction to $GL_2$ of the finite adeles, is open and compact. Then there is a real $C>0$ with the following property, for every continuous $e:\mathcal K\to\mathbb C$, every continuous compactly supported $h:GL_2(\mathbb A_{F,\infty})\to\mathbb C$ invariant under conjugation by each `archRowIsometryInclAt₀ F w k` ($w$ an infinite place, $k$ in the corresponding subgroup), and every continuous $x:GL_2(\mathbb A_F)\to\mathbb C$ that is right $U$-invariant and reproduced by $e$, i.e. $\int_{\mathcal K} e(\kappa)\,x\bigl(z\cdot\iota(\kappa)\bigr)\,d\mu(\kappa)=x(z)$ for all $z$, where $GL_2(\mathbb A_{F,\infty})$ is embedded into $GL_2(\mathbb A_F)$ by `adelicArchGLIncl` (archimedean part, trivial finite part): for every $g\in GL_2(\mathbb A_F)$ the right convolution `rightConv` of $x$ against the function $$y\mapsto\Bigl(\iint_{\mathcal K\times\mathcal K} e(\kappa_1)e(\kappa_2)\,h\bigl(\iota(\kappa_1)^{-1}\,\mathrm{glArch}(y)\,\iota(\kappa_2)^{-1}\bigr)\,d(\mu\otimes\mu)\Bigr)\cdot\mathbf 1_{\mathrm{glFin}(U)}\bigl(\mathrm{glFin}(y)\bigr),$$ that is $\int x(g y)\cdot(\cdots)\,dy$ against the adelic Haar measure `adelicGLHaar` on $GL_2(\mathbb A_F)$, equals $C\int x\bigl(g\cdot\mathrm{adelicArchGLIncl}(a)\bigr)h(a)\,d\mu a(a)$.
--
--   This is the statement that, on vectors reproduced by $e$, smoothing by the sandwiched kernel $e\star h\star e$ tensored with the indicator of the compact open level group collapses to plain archimedean smoothing by $h$, up to a positive constant coming from the volume of the level group and the comparison of the adelic Haar measure with the product of archimedean and finite Haar measures. It serves the approximate-identity step of the cuspidal spectral decomposition and is used by the approximation lemmas for cuspidal constituents such as [`AutomorphicForm.CuspidalSpectrum.exists_norm_toCarrier_sub_lt`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_norm_toCarrier_sub_lt) and its level-spherical and principal variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq.lean

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

theorem AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F)) (hιc : Continuous ι)
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing F))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing F))) [μa.IsHaarMeasure] [μa.IsMulRightInvariant]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUf : U ≤ finiteAdelicGL2Subgroup F)
    (hUo : IsOpen ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUc : IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ), Continuous e →
      ∀ (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ), Continuous h → HasCompactSupport h →
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing F)),
          h (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = h y) →
      ∀ (x : AdelicGL2 (𝓞 F) F → ℂ), Continuous x → (∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, x (g * u) = x g) →
        (∀ z : AdelicGL2 (𝓞 F) F, ∫ κ, e κ * x (z * adelicArchGLIncl F (ι κ)) ∂μ = x z) →
      ∀ g : AdelicGL2 (𝓞 F) F,
        rightConv F x
            (fun y => (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
                e p.1 * e p.2 * h ((ι p.1)⁻¹ * glArch (𝓞 F) F y * (ι p.2)⁻¹) ∂(μ.prod μ)) *
              Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F y)) g
          = C * ∫ a, x (g * adelicArchGLIncl F a) * h a ∂μa := by sorry
