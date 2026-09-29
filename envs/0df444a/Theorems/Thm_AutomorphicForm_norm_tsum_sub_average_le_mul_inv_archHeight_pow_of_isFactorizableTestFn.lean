-- Prove2me | Theorems.Thm_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
-- name    : AutomorphicForm.norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/af6dcc5c-4d48-54d3-9cff-ea5bc38b2f80
-- title:
--   Decay of rational unipotent sums minus box average in Siegel sets
-- statement:
--   Let $K$ be a number field, and let $f$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$ which is a factorizable test function, i.e. $f(g) = f_\infty(g_\infty)\, f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for some $f_\infty$ on $\mathrm{GL}_2$ of the infinite adele ring that is compactly supported and of the form $\Phi(\text{archimedean matrix entries of } g_\infty)$ for a $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space of $K$, and some $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adele ring that is locally constant with compact support. Fix real numbers $c$, $u$ and a natural number $N$. Then there is a real constant $C$ with the following property. Let $x \in \mathrm{GL}_2(\mathbb{A}_K)$ lie in the integral windowed Siegel set for $c,u$, that is: the finite component of $x$ is integral, the archimedean height $H(x) = \prod_{v \mid \infty} \bigl(|\det|_v / \mathrm{rowNormSq}\bigr)^{m_v}$ of its archimedean part is at least $c$, and at every infinite place $v$ the window quantity $\mathrm{topNormSq}/\mathrm{rowNormSq} - (|\det|_v/\mathrm{rowNormSq})^2$ of the $v$-component is at most $u^2$; assume moreover $H(x) \ge 1$. Then for every $y \in \mathrm{GL}_2(\mathbb{A}_K)$, writing $n(t) = \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$, $\mu$ for the additive Haar measure on $\mathbb{A}_K$ and $\mathrm{box}$ for the adelic box (points whose infinite part lies in a fundamental domain for the lattice basis of $K$ and whose finite part is everywhere integral),
--   $$\Bigl\| \sum_{\beta \in K} f(x^{-1} n(\beta) y) \; - \; \mu(\mathrm{box})^{-1} \int_{\mathbb{A}_K} f(x^{-1} n(t) y)\, d\mu(t) \Bigr\| \le C\, \bigl(H(x)^{-1}\bigr)^{N}.$$
--   The constant $C$ depends only on $K$, $f$, $c$, $u$ and $N$; the bound is uniform in $x$ in the Siegel set with $H(x)\ge 1$ and in $y$ throughout the group.
--
--   This is the Godement-type estimate showing that, high in a Siegel set, the sum of a factorizable test function over the rational unipotent translates differs from its mean over one adelic period by $O(H(x)^{-N})$ for every $N$, the error term being what adelic Poisson summation produces from the nonzero rational frequencies. It is the analytic input for the bounds on right convolution of cuspidal automorphic functions by test functions, and hence for the construction of levels at which cuspidal Hecke eigenfunctions are realizable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn.lean

import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
  AutomorphicForm AutomorphicForm.WindowedSiegel MeasureTheory

theorem AutomorphicForm.norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f) (c u : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ x ∈ integralWindowedSiegelSet K c u,
      1 ≤ archHeight K (glArch (𝓞 K) K x) →
      ∀ (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        ‖(∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
          - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)‖
          ≤ C * (archHeight K (glArch (𝓞 K) K x))⁻¹ ^ N := by sorry
