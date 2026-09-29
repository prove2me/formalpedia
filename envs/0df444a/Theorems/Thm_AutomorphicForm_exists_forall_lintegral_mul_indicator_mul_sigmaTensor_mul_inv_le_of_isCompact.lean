-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_mul_indicator_mul_sigmaTensor_mul_inv_le_of_isCompact
-- name    : AutomorphicForm.exists_forall_lintegral_mul_indicator_mul_sigmaTensor_mul_inv_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/3acbe784-fc0e-5556-9b51-f0f698d1c9f2
-- title:
--   Uniform bound for archimedean twisted-orbital volumes
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so $L/K$ is cyclic with generator $\sigma$). Write $K_\infty =$ `InfiniteAdeleRing K` and $E = L \otimes_K K_\infty$, both unit groups being equipped with Borel measurable structures; let $\nu_A$ be a Haar measure on $K_\infty^\times$ and $\rho$ a Haar measure on $E^\times$. Let $\beta : \mathrm{GL}_2(E) \to \mathbb{R}$ be measurable for the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57) on $\mathrm{GL}_2(E)$, with $\beta \ge 0$, and normalised so that for every pair $a = (a_1,a_2) \in E^\times \times E^\times$ one has $\int_{(K_\infty^\times)^2} \beta\bigl(\mathrm{diag}(1 \otimes p_1, 1 \otimes p_2)\,\mathrm{diag}(a_1,a_2)\bigr)\, d(\nu_A \otimes \nu_A)(p) = 1$; here $\mathrm{diag}$ is `diagUnits2`, the diagonal embedding of a pair of units into $\mathrm{GL}_2$, and the first factor is the image of $\mathrm{diag}(p_1,p_2)$ under the map [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) on $\mathrm{GL}_2$ induced by $\mathrm{Algebra.TensorProduct.includeRight} : K_\infty \to L \otimes_K K_\infty$. Finally let $\Omega \subseteq E^\times \times E^\times$ be compact. The conclusion is that there exists $V \in [0,\infty]$ with $V \neq \infty$ such that for every $e = (e_1,e_2) \in E^\times \times E^\times$ the lower Lebesgue integral $$\int^{-}_{(E^\times)^2} \mathrm{ofReal}\bigl(\beta(\mathrm{diag}(a_1,a_2))\bigr)\cdot \mathbf{1}_\Omega\bigl(e_1\,\sigma(a_1)\,a_1^{-1},\; e_2\,\sigma(a_2)\,a_2^{-1}\bigr)\, d(\rho \otimes \rho)(a) \le V,$$ where $\sigma$ acts on $E^\times$ through the units functor applied to the ring homomorphism $\sigma \otimes \mathrm{id}$ on $L \otimes_K K_\infty$ ([`AutomorphicForm.sigmaTensor`](def/AutomorphicForm_TwistedOrbital.html#L199)), and $\mathbf{1}_\Omega$ is the $\{0,1\}$-valued indicator of $\Omega$ in $[0,\infty]$.
--
--   This is the archimedean volume estimate underlying the convergence of twisted orbital integrals on the diagonal torus for a cyclic extension $L/K$: the $\beta$-weighted measure of the set of $a$ with $e\cdot\sigma(a)/a$ in a fixed compact window is bounded uniformly in the translating parameter $e$. It rests on the companion result that a compact set of values of $a \mapsto \sigma(a)a^{-1}$ forces $a$ into a compact set modulo the image of $K_\infty^\times$, and it feeds the archimedean bound for twisted orbital integrals used in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_mul_indicator_mul_sigmaTensor_mul_inv_le_of_isCompact.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_forall_lintegral_mul_indicator_mul_sigmaTensor_mul_inv_le_of_isCompact
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρ : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (β : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hβm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ1 : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            β (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * diagUnits2 a.1 a.2)
          ∂(νA.prod νA) = 1)
    (Ω : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ)) (hΩ : IsCompact Ω) :
    ∃ V : ℝ≥0∞, V ≠ ∞ ∧ ∀ e : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
          ENNReal.ofReal (β (diagUnits2 a.1 a.2)) *
            Ω.indicator (fun _ => (1 : ℝ≥0∞))
              (e.1 * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹, e.2 * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) ∂(ρ.prod ρ) ≤ V := by sorry
