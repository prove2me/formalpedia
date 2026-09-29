-- Prove2me | Theorems.Thm_AutomorphicForm_mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul
-- name    : AutomorphicForm.mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/9ccfca44-079d-5f96-8063-606b275c760a
-- title:
--   Compact averaging preserves isotypy, gives K-finiteness, decreases mass
-- statement:
--   Let $K$ be a number field and $\alpha,\beta$ real numbers. Let $\Phi_0$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ which is a fundamental domain, in the sense of `IsFundamentalDomain`, for the action of the image of $\mathrm{GL}_2(K)$ under `globalPoints` on the restriction of the Haar measure `adelicGLHaar` to the slab $\{g : \lVert\det g\rVert \in [\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is the idele norm given by the value of the `distribHaarChar` of $\mathbb{A}_K$, and assume moreover $\Phi_0$ is contained in that slab. Let `pins` be the carrier data `productionPinsOf` attached to $K$ with domain $\Phi_0$, Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, central subgroup $\top$, level subgroups $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, Hecke generators $v \mapsto \mathrm{heckeGen}(v)$, and the additive Haar measure conditioned on `adelicBox K`; let $\xi$ be a homomorphism from its central subgroup to $\mathbb{C}^\times$, $N$ an ideal of $\mathcal O_K$, $S$ a finite set of finite places, and $\Psi$ a Hecke eigensystem over $\mathbb{C}$ (a level, nonzero, together with families $a_v,b_v$). Let $\kappa$ be a continuous, nonnegative real function on the subgroup $\mathrm{maximalCompactAt}\,K\,\emptyset$ (the adelic maximal compact intersected with the kernels of all finite components, i.e. with trivial finite part) with integral $1$ against the Haar measure `maximalCompactAtHaar`, and assume that the left translates $k \mapsto \kappa(ak)$ all lie in the real span of one finite set of functions. Let $f$ lie in `isotypicCuspSubmodule`, the $\mathbb{C}$-span of the functions satisfying `IsIsotypicCuspFormAt` for these data. Then the average $x \mapsto \int \kappa(k) f(xk)\,dk$ again lies in that submodule, satisfies `IsArchKFinite` (the predicate `IsArchKFiniteAt` at every infinite place of $K$), and its squared $L^2$ mass over $\Phi_0$, computed as a lower Lebesgue integral of $\lVert\cdot\rVert^2$ in $[0,\infty]$ against `adelicGLHaar`, is at most that of $f$.
--
--   This is the smoothing step in the archimedean direction: convolution on the right by an approximate-identity kernel on the archimedean maximal compact subgroup produces a $K$-finite vector inside the same isotypic space of cusp forms without increasing the $L^2$ mass over a slab fundamental domain. It is used in the construction of $K$-finite approximants to a given isotypic cusp form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul
    (K : Type) [Field K] [NumberField K] (α β : ℝ)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (ξ : (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (κ : ↥(maximalCompactAt K ∅) → ℝ) (hκc : Continuous κ) (hκ0 : ∀ k, 0 ≤ κ k) (hκ1 : ∫ k, κ k ∂(maximalCompactAtHaar K ∅) = 1)
    (hκfin : ∃ s : Finset (↥(maximalCompactAt K ∅) → ℝ), ∀ a : ↥(maximalCompactAt K ∅),
      (fun k => κ (a * k)) ∈ Submodule.span ℝ (s : Set (↥(maximalCompactAt K ∅) → ℝ)))
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : f ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ) :
    (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ ∧
    IsArchKFinite K (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) ∧
    ∫⁻ x in Φ₀, (‖∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ∫⁻ x in Φ₀, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
