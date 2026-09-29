-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_adelicGLHaar_eq_mul_lintegral_unipotentQuotientMeasure
-- name    : AutomorphicForm.lintegral_adelicGLHaar_eq_mul_lintegral_unipotentQuotientMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/d0b9132b-d876-56d9-b40d-849362d39517
-- title:
--   Unfolding the Haar integral on GL₂(A_K) along N(A_K)
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K`, and write $G =$ `AdelicGL2 (𝓞 K) K` for $\mathrm{GL}_2(\mathbb{A}_K)$; both $\mathbb{A}_K$ and $G$ carry their Borel $\sigma$-algebras, $G$ the Haar measure `adelicGLHaar` and $\mathbb{A}_K$ the additive Haar measure `adelicAddHaar`. Let $f \colon G \to [0,\infty]$ be a measurable function (no integrability or invariance is assumed). Put $V =$ `adelicAddHaar (𝓞 K) K (adelicBox K)`, the measure of the set of adeles whose infinite component lies in the fundamental domain of the lattice basis of the mixed space and whose finite component is integral at every finite place. Let $N \le G$ be the image of $x \mapsto n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ on $\mathbb{A}_K$, let `UnipotentQuotient K` be the quotient of $G$ by the orbit relation of $N$, and let $\nu =$ `unipotentQuotientMeasure K` be the image under the quotient map of `adelicGLHaar` weighted by the density attached to the Haar measure on $N$ obtained by transporting $V^{-1} \cdot$ `adelicAddHaar` along $x \mapsto n(x)$. Then $$\int^{-} f \, d(\mathrm{adelicGLHaar}) = V^{-1} \int^{-}_{q} \Big( \int^{-}_{x \in \mathbb{A}_K} f\big(n(x) \cdot q^{\mathrm{out}}\big) \, dx \Big) d\nu(q),$$ where $q^{\mathrm{out}}$ is the representative of the coset $q$ given by `Quotient.out`. The identity is an equality in $[0,\infty]$, so both sides may be infinite.
--
--   This is the unfolding of the Haar integral on $\mathrm{GL}_2(\mathbb{A}_K)$ along the unipotent radical of the standard Borel subgroup, the measure-theoretic step underlying Whittaker–Fourier expansions and the Rankin–Selberg method, specialised to the concrete normalisation in which the Haar measure of $N(\mathbb{A}_K)$ is the transport of the additive Haar measure of $\mathbb{A}_K$ rescaled by the volume of the adelic box. It is used in the estimates on class sums and on window masses for isotypic cusp forms, namely by [`AutomorphicForm.ClassSumGrowth.exists_forall_le_classSum_of_classCarriesMass`](thm.html#AutomorphicForm.ClassSumGrowth.exists_forall_le_classSum_of_classCarriesMass) and [`AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule`](thm.html#AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_adelicGLHaar_eq_mul_lintegral_unipotentQuotientMeasure.lean

import Definitions.Def_AutomorphicForm_UnipotentQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem AutomorphicForm.lintegral_adelicGLHaar_eq_mul_lintegral_unipotentQuotientMeasure
    (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ *
        ∫⁻ q, (∫⁻ x, f (unipotentGL2 x * q.out) ∂(adelicAddHaar (𝓞 K) K))
          ∂(unipotentQuotientMeasure K) := by sorry
