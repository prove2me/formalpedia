-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_forall_isOrbitalIntegralOn_mul_centralScalar_of_mem_ellipticCell
-- name    : AutomorphicForm.exists_continuous_hasCompactSupport_forall_isOrbitalIntegralOn_mul_centralScalar_of_mem_ellipticCell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/e5816ad7-c32a-524e-86a6-796cec665abb
-- title:
--   Elliptic orbital integrals of central translates, continuous and compactly supported in u
-- statement:
--   Let $K$ be a number field, and let $\gamma_0 \in \mathrm{GL}_2(K)$ lie in [`AutomorphicForm.ellipticCell K`](def/AutomorphicForm_GL2ConjugacyCells.html#L35), that is, the characteristic polynomial of the matrix underlying $\gamma_0$ has no root in $K$. Write $\gamma =$ `globalPoints` $\gamma_0$ for the image of $\gamma_0$ in $\mathrm{GL}_2(\mathbb{A}_K)$ under the entrywise map induced by $K \to \mathbb{A}_K$, and let $\tau$ be a Haar measure on the centraliser $T = \mathrm{Cent}_{\mathrm{GL}_2(\mathbb{A}_K)}(\{\gamma\})$, taken with its Borel $\sigma$-algebra. Let $c_0 \in \mathbb{R}_{\ge 0}$, and let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support. Then there exists $G : \mathbb{A}_K^{\times} \to \mathbb{C}$, continuous and with compact support, such that for every idele $u$ the value $G(u)$ is an orbital integral at $\gamma$ of the central translate $g \mapsto f(g \cdot \mathrm{diag}(u,u))$ with respect to the measure $c_0 \cdot$ `adelicGLHaar` and the torus measure $\tau$: for each $u$ there is $w : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{R}$, non-negative, measurable and compactly supported, with $\int_T w(tx)\,\mathrm{d}\tau(t) = 1$ for every $x$ at which $f(x^{-1}\gamma x \cdot \mathrm{diag}(u,u)) \neq 0$, and $$G(u) = \int_{\mathrm{GL}_2(\mathbb{A}_K)} f\bigl(x^{-1}\gamma x \cdot \mathrm{diag}(u,u)\bigr)\, w(x)\, \mathrm{d}(c_0 \cdot \text{Haar})(x).$$
--
--   This provides the regularity in the central parameter needed for the elliptic terms of the adelic trace formula: the global orbital integral of an elliptic element, viewed as a function of the central idele by which the test function is translated, is continuous and compactly supported. It feeds the computation of elliptic contributions over a fundamental domain and the comparison of twisted and ordinary orbital integrals in the base-change argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_hasCompactSupport_forall_isOrbitalIntegralOn_mul_centralScalar_of_mem_ellipticCell.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open NumberField NumberField.AdelicHaar
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.exists_continuous_hasCompactSupport_forall_isOrbitalIntegralOn_mul_centralScalar_of_mem_ellipticCell
    (K : Type) [Field K] [NumberField K]
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K)
    (τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} :
      Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) [τ.IsHaarMeasure]
    (c₀ : NNReal)
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ G : (AdeleRing (𝓞 K) K)ˣ → ℂ, Continuous G ∧ HasCompactSupport G ∧
      ∀ u : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀) τ
          (fun g => f (g * AutomorphicForm.centralScalar (𝓞 K) K u)) (G u) := by sorry
