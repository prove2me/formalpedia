-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_isRegularSemisimple
-- name    : AutomorphicForm.isOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/c7caa35c-1d69-51bf-9c04-a45694333b69
-- title:
--   Linearity and measurability of adelic orbital integrals
-- statement:
--   Let $K$ be a number field, and equip the idele group $(\mathbb{A}_K)^\times$ with a measurable space structure which is the Borel structure of its topology; the groups $\mathrm{GL}_2(\mathbb{A}_K)$ and the centraliser occurring below carry their Borel structures, and $\mathrm{GL}_2(\mathbb{A}_K)$ carries the Haar measure `adelicGLHaar`. Let $s$ be a finite index set of indices in $\iota$, $c : \iota \to \mathbb{C}$, and let $\gamma \in \mathrm{GL}_2(\mathbb{A}_K)$ be regular semisimple in the sense that $\mathrm{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $\mathbb{A}_K$. Let $\tau$ be a Haar measure on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$. Let $f : \iota \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be such that $f_i$ is continuous with compact support for each $i \in s$, and let $I : \iota \to (\mathbb{A}_K)^\times \to \mathbb{C}$ be such that, for every $i \in s$ and every idele $z$, the number $I_i(z)$ is an orbital integral of $g \mapsto f_i(\mathrm{diag}(z,z)\,g)$ at $\gamma$: that is, there is a weight $w : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{R}$ which is non-negative, measurable and compactly supported, satisfies $\int_{T_\gamma} w(tx)\,d\tau(t) = 1$ for every $x$ at which the function does not vanish at $x^{-1}\gamma x$, and for which $I_i(z) = \int f_i(\mathrm{diag}(z,z)\,x^{-1}\gamma x)\,w(x)\,d\mu(x)$. The conclusion is twofold: first, for every idele $z$ the number $\sum_{i \in s} c_i I_i(z)$ is, in the same sense, an orbital integral at $\gamma$ of $g \mapsto \sum_{i \in s} c_i f_i(\mathrm{diag}(z,z)\,g)$; second, $I_i$ is measurable on $(\mathbb{A}_K)^\times$ for every $i \in s$.
--
--   This records the canonicity of adelic orbital integrals at a regular semisimple element: because the value does not depend on the choice of section weight, it is linear in the test function and depends measurably on the central twisting parameter. It is used in the comparison of hyperbolic contributions, in the derivation of the slope identity [`AutomorphicForm.exists_forall_hyperbolicSlope_eq_mul_sum_slotFamilyCoeff_mul_hyperbolicSlope_of_eq_affine`](thm.html#AutomorphicForm.exists_forall_hyperbolicSlope_eq_mul_sum_slotFamilyCoeff_mul_hyperbolicSlope_of_eq_affine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_isRegularSemisimple.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.isOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure]
    (f : ι → AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i) ∧ HasCompactSupport (f i))
    (I : ι → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hI : ∀ i ∈ s, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) γ τ
        (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K => f i (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (I i z)) :
    (∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) γ τ
        (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
          ∑ i ∈ s, c i * f i (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (∑ i ∈ s, c i * I i z)) ∧
    (∀ i ∈ s, Measurable (I i)) := by sorry
