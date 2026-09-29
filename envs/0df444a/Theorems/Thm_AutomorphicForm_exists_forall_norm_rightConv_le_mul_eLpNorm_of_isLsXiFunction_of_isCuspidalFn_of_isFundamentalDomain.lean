-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
-- name    : AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/e683198e-9b63-575d-835e-d926061919c6
-- title:
--   Uniform bound for right convolution on centre-cut Siegel windows
-- statement:
--   Let $K$ be a number field, let $\xi$ be a group homomorphism from the full subgroup $\top$ of the idele units $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, and let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be factorizable in the sense of `IsFactorizableTestFn`, that is $f(g) = f_\infty(g_\infty)\, f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean test factor $f_\infty$ and a finite test factor $f_{\mathrm{fin}}$. Fix reals $c, u, d_1, d_2$ with $c > 0$ and $d_1 > 0$, a finite set $T$ of points of $\mathrm{GL}_2(\mathbb{A}_K)$, and reals $\alpha < \beta$ with $\beta > 0$; let $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be a measure-theoretic fundamental domain for the left action of the image of $\mathrm{GL}_2(K)$ under `globalPoints` on the adelic Haar measure of $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to the slab $\{g : \|\det g\|_{\mathbb{A}} \in [\alpha,\beta]\}$, the norm being the idele norm given by the distributive Haar character. Then there is a real constant $C$, depending only on these data, such that for every $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ which is left invariant under $\mathrm{GL}_2(K)$ and satisfies $\varphi(z I_2 \cdot g) = \xi(z)\varphi(g)$ for all ideles $z$ and all $g$, whose constant term along the family $t \mapsto \begin{pmatrix}1&t\\0&1\end{pmatrix}$ vanishes at every point, the defining integral being taken for the adelic additive Haar measure conditioned on the adelic box (adeles with infinite part in the infinite box and integral finite part), which is continuous, and which is square-integrable for the Haar measure restricted to $\Phi_0$, one has $\|(\varphi * f)(g)\| \le C \cdot \left(\int_{\Phi_0} |\varphi|^2\right)^{1/2}$ for every $g$ lying in one of the right translates $\{s x : s \in \Sigma\}$, $x \in T$, of the centre-cut Siegel set $\Sigma$ with parameters $c, u, d_1, d_2$ (finite component in the integral subgroup, every archimedean local height at least $c$, every archimedean $x$-window square at most $u^2$, and every archimedean determinant norm in $[d_1,d_2]$). Here $(\varphi * f)(g) = \int \varphi(gy) f(y)\, dy$ is the right convolution, and the right-hand side uses the real value of the $L^2$ norm of $\varphi$ over $\Phi_0$.
--
--   This is the uniform boundedness of the smoothing operator $R(f)$ from the $L^2$-norm over a fundamental domain of a determinant slab to the supremum norm over a finite union of translated centre-cut Siegel sets, valid for all continuous cuspidal functions of central character $\xi$ with one and the same constant. It is the form of the bound used in the growth estimates for class sums and in the identification of cuspidal constituents inside level-invariant submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
  AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ C : ℝ, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ ξ φ →
        IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ →
          Continuous φ →
            MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) →
              ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂),
                ‖rightConv K φ f g‖ ≤
                  C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)).toReal := by sorry
