-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa
-- name    : AutomorphicForm.exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/a488ed5b-7104-5bc5-af42-25f3be5bbb27
-- title:
--   Iwasawa coordinates for Haar measure on GL₂(L⊗_K Kᵥ)
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a height one prime of $\mathcal{O}_K$, and write $E = L \otimes_K K_v$ for the tensor product of $L$ with the $v$-adic completion of $K$, equipped with a measurable structure that is the Borel one and with an additive Haar measure $\nu$. The group $\mathrm{GL}_2(E)$ carries the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57), and $\mu =$ [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169) denotes the Haar measure of $\mathrm{GL}_2(E)$ normalised by the compact open subgroup [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) of those $g$ for which both $g$ and $g^{-1}$ have all entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$ in $E$. The assertion is that there exists a real $\kappa > 0$ such that for every measurable $\Phi : \mathrm{GL}_2(E) \to \mathbb{C}$ that is $\mu$-integrable,
--   $$\int_{\mathrm{GL}_2(E)} \Phi \, d\mu = \kappa \int_{E \times E} F(p_1,p_2)\, d(\nu \otimes \nu),$$
--   where $F(p_1,p_2) = 0$ unless both $p_1$ and $p_2$ are units of $E$, in which case
--   $$F(p_1,p_2) = \|N_{E/K_v}(p_1p_2)\|^{-1} \int_E \int_{\mathcal{K}} \Phi\big(\mathrm{diag}(p_1,p_2)\, n(\xi)\, k\big)\, d\mu(k)\, d\nu(\xi),$$
--   with $\mathcal{K}$ the above integral set, $n(\xi) = \begin{pmatrix} 1 & \xi \\ 0 & 1\end{pmatrix}$ ([`AutomorphicForm.unipotentGL2`](def/AutomorphicForm_ConstantTerm.html#L17)), $\mathrm{diag}(p_1,p_2)$ the image of the two units under `diagUnits2`, and $\|\cdot\|$ the norm on $K_v$ applied to the algebra norm of $E$ over $K_v$.
--
--   This is the decomposition of the Haar measure of $\mathrm{GL}_2(E)$ in Iwasawa coordinates $g = \mathrm{diag}(p_1,p_2)\,n(\xi)\,k$, with modulus $\|N_{E/K_v}(p_1p_2)\|^{-1}$, in its complex-valued Bochner form; it is deduced from the corresponding identity for $[0,\infty]$-valued integrands and iterated lower integrals. It is used in the computation of twisted orbital integrals at the place $v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    ∃ κ : ℝ, 0 < κ ∧ ∀ Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      Measurable Φ → Integrable Φ (AutomorphicForm.semiLocalHaar K L v) →
      ∫ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v) =
        (κ : ℂ) * ∫ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
          (if h : IsUnit p.1 ∧ IsUnit p.2 then
            ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) *
              ∫ ξ : (L ⊗[K] v.adicCompletion K), ∫ k in AutomorphicForm.semiLocalIntegralSet K L v,
                Φ (diagUnits2 h.1.unit h.2.unit * AutomorphicForm.unipotentGL2 ξ * k)
                ∂(AutomorphicForm.semiLocalHaar K L v) ∂ν
           else 0) ∂(ν.prod ν) := by sorry
