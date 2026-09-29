-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain
-- name    : AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/755bfa92-1724-5b95-91b2-4067a7d82c20
-- title:
--   Square-mass bound on Siegel sets against a slab fundamental domain
-- statement:
--   Let $K$ be a number field, let $\chi$ be a group homomorphism from the full subgroup $\top$ of the idele group $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ (no continuity or unitarity being assumed), and let $C\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be compact. Fix reals $c',u',d_1',d_2'$ with $c'>0$ and $d_1'>0$, and reals $\alpha<\beta$ with $\beta>0$. Let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be a measure-theoretic fundamental domain for the action of the range of `globalPoints`, i.e. the image of $\mathrm{GL}_2(K)$ under the entrywise map $K\to\mathbb{A}_K$, on the Haar measure `adelicGLHaar` of $\mathrm{GL}_2(\mathbb{A}_K)$ (for its Borel $\sigma$-algebra) restricted to the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$, the idele norm being the value of the distributive Haar character of $\mathbb{A}_K$ at $\det g$. Then there exist $T_1\in\mathbb{R}$, $A\in\mathbb{N}$ and $M\in\mathbb{R}$ such that for every continuous $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfying `IsLsXiFunction`, that is $\varphi(\gamma g)=\varphi(g)$ for all $\gamma\in \mathrm{GL}_2(K)$ (embedded adelically) and $\varphi(zI\cdot g)=\chi(z)\varphi(g)$ for all ideles $z$, and for every $x$ in the centre-cut Siegel set with parameters $c',u',d_1',d_2'$ — its finite part lies in `finiteIntegralGL2`, each local height $\mathrm{localHeight}$ of the component at an infinite place $w$ is $\ge c'$, each squared window $\mathrm{xWindowSq}$ is $\le u'^2$, and each $\mathrm{archDetNorm}_w(x)$ lies in $[d_1',d_2']$ — such that $T_1 < H(x)$, where $H(x)=\prod_w \mathrm{localHeight}(x_w)^{[K_w:\mathbb{R}]}$ is the archimedean height of the archimedean component of $x$, one has $$\int_{R(x)} \|\varphi(y)\|^2\,d\mu(y) \le M\,H(x)^{A}\int_{\Phi_0}\|\varphi(y)\|^2\,d\mu(y)$$ as an inequality of lower Lebesgue integrals in $[0,\infty]$ for $\mu=$ `adelicGLHaar`, the right-hand factor being $\mathrm{ofReal}(M\,H(x)^A)$, where $R(x)$ is the set of products $\begin{pmatrix}1&t\\0&1\end{pmatrix} x\,k$ with $t$ in the closure of the adelic box (archimedean part in the fundamental parallelotope of the lattice basis, finite part integral) and $k\in C$.
--
--   This is the uniform square-mass comparison used in the analytic theory of adelic automorphic forms on $\mathrm{GL}_2$: the $L^2$-mass of a function with central character over a region swept out from a point of a Siegel set by unipotent translations and a fixed compact set is bounded by a power of the archimedean height times its mass over a single fundamental domain for $\mathrm{GL}_2(K)$ acting on a determinant-norm slab, with constants independent of the form. It is cited in the bound for the norm of right convolution against the $L^2$-norm of a cuspidal form with central character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
  AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁')
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ (T₁ : ℝ) (A : ℕ) (M : ℝ), ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂',
          T₁ < archHeight K (glArch (𝓞 K) K x) →
            ∫⁻ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
              unipotentGL2 t * x * c) (closure (adelicBox K)) C,
                (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
              ≤ ENNReal.ofReal (M * archHeight K (glArch (𝓞 K) K x) ^ A) *
                ∫⁻ y in Φ₀, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
