-- Prove2me | Theorems.Thm_AutomorphicForm_measurable_lintegral_unipotentGL2_mul_out
-- name    : AutomorphicForm.measurable_lintegral_unipotentGL2_mul_out
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/353ac3d2-d5fe-51f3-bfcc-c3bccecae17a
-- title:
--   Measurability of unipotent integrals on N(A_K)backslashGL₂(A_K)
-- statement:
--   Let $K$ be a number field, with adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K` carried by its Borel $\sigma$-algebra, and let $\mathrm{GL}_2(\mathbb{A}_K) =$ `AdelicGL2 (𝓞 K) K` carry the Borel $\sigma$-algebra of its topology. Let $f \colon \mathrm{GL}_2(\mathbb{A}_K) \to [0,\infty]$ be a measurable function, and write $n(x)$ for the unipotent matrix $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$, viewed as an element of $\mathrm{GL}_2$ of whatever ring $x$ lies in. Assume $f$ is left invariant under the rational unipotent subgroup: $f\big(n(k)\cdot g\big) = f(g)$ for every $k \in K$ and every $g \in \mathrm{GL}_2(\mathbb{A}_K)$, where $n(k)$ is pushed into $\mathrm{GL}_2(\mathbb{A}_K)$ by the map `globalPoints` induced entrywise by $K \to \mathbb{A}_K$. Let $\mu$ be the additive Haar measure of $\mathbb{A}_K$ conditioned on the box `adelicBox K`, that is, the set of adeles whose infinite part lies in the fundamental domain of the lattice basis of the mixed space and whose finite part is everywhere integral. Then the function $$q \longmapsto \int^{-} f\big(n(x)\cdot q.\mathrm{out}\big)\, d\mu(x)$$ on `UnipotentQuotient K`, the quotient of $\mathrm{GL}_2(\mathbb{A}_K)$ by the orbit relation of the subgroup of all $n(x)$ with $x \in \mathbb{A}_K$, with $q.\mathrm{out}$ a chosen representative of $q$, is measurable for the quotient $\sigma$-algebra (a set is measurable exactly when its preimage in $\mathrm{GL}_2(\mathbb{A}_K)$ is Borel).
--
--   This is the measurability input for the unfolding step along the unipotent radical of the standard Borel subgroup of $\mathrm{GL}_2$ over $\mathbb{A}_K$: invariance of $f$ under $n(K)$ makes the integral over the box independent of the representative chosen in each $n(\mathbb{A}_K)$-coset, so the function descends to the coset space and inherits measurability. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, where global integrals are rewritten as integrals over $N(\mathbb{A}_K)\backslash\mathrm{GL}_2(\mathbb{A}_K)$ against Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_measurable_lintegral_unipotentGL2_mul_out.lean

import Definitions.Def_AutomorphicForm_UnipotentQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem AutomorphicForm.measurable_lintegral_unipotentGL2_mul_out
    (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f)
    (hfK : ∀ (k : K) (g : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K (unipotentGL2 k) * g) = f g) :
    Measurable fun q : UnipotentQuotient K =>
      ∫⁻ x, f (unipotentGL2 x * q.out) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) := by sorry
