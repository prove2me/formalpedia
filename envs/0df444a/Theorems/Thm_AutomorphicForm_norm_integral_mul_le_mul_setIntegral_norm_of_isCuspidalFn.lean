-- Prove2me | Theorems.Thm_AutomorphicForm_norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn
-- name    : AutomorphicForm.norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/33a4bbae-f7fc-53f0-980b-78e3ad49e498
-- title:
--   Cuspidality bound for int φ(y)f(x⁻¹y) on GL₂(A_K)
-- statement:
--   Let $K$ be a number field, $\mathbb{A}_K$ its adele ring, and equip $\mathbb{A}_K$ and $\mathrm{GL}_2(\mathbb{A}_K)$ with their Borel $\sigma$-algebras, writing $\mu_{\mathbb{A}} =$ `adelicAddHaar` for the additive Haar measure on $\mathbb{A}_K$ and $\mu =$ `adelicGLHaar` for the Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$. For $t \in \mathbb{A}_K$ let $n(t) = \begin{pmatrix}1&t\\0&1\end{pmatrix}$ (`unipotentGL2`), and let $B =$ `adelicBox K` be the set of adeles whose infinite component lies in the preimage, under the identification of $\mathbb{A}_{K,\infty}$ with the mixed space, of the fundamental domain of the lattice basis of $\mathcal{O}_K$, and whose finite component is integral at every height-one prime. Let $\varphi, f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ and $x \in \mathrm{GL}_2(\mathbb{A}_K)$, and assume: $\varphi(n(\beta)y) = \varphi(y)$ for all $\beta \in K$ (embedded in $\mathbb{A}_K$) and all $y$; $\varphi$ is locally integrable for $\mu$; $\varphi$ is cuspidal along $n$ with respect to the conditioning $\mu_{\mathbb{A}}[\,\cdot\mid B]$ of $\mu_{\mathbb{A}}$ on $B$, i.e. `constantTerm` of $\varphi$, the integral of `constantTermIntegrand unipotentGL2 φ g` against that conditional measure, vanishes for every $g$; $f$ is continuous with compact support. Let $\varepsilon \in \mathbb{R}$ be such that for every $y$,
--   $$\Bigl\| \sum_{\beta \in K} f(x^{-1} n(\beta) y) \;-\; \mu_{\mathbb{A}}(B)^{-1} \int_{\mathbb{A}_K} f(x^{-1} n(t) y)\, d\mu_{\mathbb{A}}(t) \Bigr\| \le \varepsilon,$$
--   the scalar $\mu_{\mathbb{A}}(B)^{-1}$ being formed from the real number $\mu_{\mathbb{A}}(B)$ viewed in $\mathbb{C}$. Then
--   $$\Bigl\| \int \varphi(y) f(x^{-1}y)\, d\mu(y) \Bigr\| \le \varepsilon \int_R \|\varphi(y)\|\, d\mu(y),$$
--   where $R$ is the set of products $n(t)\,x\,c$ with $t \in \overline{B}$ and $c$ in the topological support of $f$.
--
--   This is the basic estimate expressing that, for a function left invariant under the rational unipotent subgroup whose constant term along that subgroup vanishes, the pairing of $\varphi$ with a right translate of a compactly supported $f$ is controlled by how well the sum of $f$ over the rational unipotent orbit approximates its unipotent average, times the $L^1$-mass of $\varphi$ over a compact set. It is obtained from the unfolding identity [`AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn`](thm.html#AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn) together with the finiteness of the set of rational points landing in a compact subset of $\mathbb{A}_K$, and feeds the bounds on right convolutions of cusp forms used in the analytic input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm MeasureTheory
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (ε : ℝ)
    (hP : ∀ y, ‖(∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
        - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)‖ ≤ ε) :
    ‖∫ y, φ y * f (x⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ ε * ∫ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * x * c) (closure (adelicBox K)) (tsupport f),
          ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
