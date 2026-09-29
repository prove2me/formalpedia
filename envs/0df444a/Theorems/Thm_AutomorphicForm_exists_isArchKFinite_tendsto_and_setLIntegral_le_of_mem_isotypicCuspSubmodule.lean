-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule
-- name    : AutomorphicForm.exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/0994c0ce-ea26-561a-a84c-4925a3869e57
-- title:
--   Archimedean-finite smoothing inside an isotypic cusp space
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be real numbers, and let $\Phi_0$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ which is a fundamental domain for the image of $\mathrm{GL}_2(K) \to \mathrm{GL}_2(\mathbb{A}_K)$ (the map `globalPoints`, induced by $K \to \mathbb{A}_K$) with respect to the adelic Haar measure `adelicGLHaar` restricted to the determinant strip $\{g : \lVert \det g\rVert_{\mathbb{A}} \in [\alpha,\beta]\}$, where $\lVert\cdot\rVert_{\mathbb{A}}$ is the idele norm defined by the module of the translation action on $\mathbb{A}_K$, and which is itself contained in that strip. Fix a character $\xi$ of the group $\mathrm{Z}$ of the pins `productionPinsOf` built from $\Phi_0$, the levels $U(N) =$ `levelOne` $N \sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` $v$ and the box `adelicBox` (so $\mathrm{Z}$ is all of $\mathbb{A}_K^\times$, the measure is `adelicGLHaar` and the auxiliary adelic measure is Haar measure conditioned on the box), an ideal $N$ of $\mathcal{O}_K$, a finite set $S$ of finite places, and a Hecke eigensystem $\Psi$ over $\mathbb{C}$ (a nonzero level ideal together with families $a_v, b_v$). Let $f$ lie in `isotypicCuspSubmodule`, the $\mathbb{C}$-span of the continuous functions $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfying `IsSmoothCuspAutomorphicFnAt` for these pins and $\xi$, right invariant under $U(N)$, eigen for the Hecke coset operator at `heckeGen` $v$ with eigenvalue $a_v$ for every $v \notin S$, and satisfying $\varphi(z(\det(\mathrm{heckeGen}\,v))g) = b_v\,\varphi(g)$ for $v \notin S$. Then there is a sequence $\varphi_n$ of functions, each again in that submodule, each archimedean $K$-finite in the sense that for every infinite place $w$ the right translates of $\varphi_n$ under `archRowIsometrySubgroup` $K\,w$ span a finite-dimensional space, such that $\varphi_n(g) \to f(g)$ for every $g$, and such that for every $n$ one has $\int^-_{\Phi_0} \lVert\varphi_n\rVert^2 \le \int^-_{\Phi_0} \lVert f\rVert^2$ for `adelicGLHaar`, the lower Lebesgue integrals being valued in $[0,\infty]$.
--
--   This is the smoothing step which replaces an arbitrary element of an isotypic space of adelic cusp forms by archimedean $K$-finite approximants, without increasing the $L^2$-mass over the chosen fundamental domain; it is the device by which statements proved for $K$-finite vectors extend to the whole isotypic space. It is used in the estimate [`AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre`](thm.html#AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
    AutomorphicForm.exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule
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
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : f ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ) :
    ∃ φ : ℕ → AdelicGL2 (𝓞 K) K → ℂ,
      (∀ n, φ n ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ₀
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξ N S Ψ) ∧
      (∀ n, IsArchKFinite K (φ n)) ∧
      (∀ g, Filter.Tendsto (fun n => φ n g) Filter.atTop (nhds (f g))) ∧
      (∀ n, ∫⁻ x in Φ₀, (‖φ n x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
              ≤ ∫⁻ x in Φ₀, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by sorry
