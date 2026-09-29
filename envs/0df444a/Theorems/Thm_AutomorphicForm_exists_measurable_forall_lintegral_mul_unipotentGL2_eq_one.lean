-- Prove2me | Theorems.Thm_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one
-- name    : AutomorphicForm.exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/aa3ffab9-1234-5295-afa0-dceef53d5dcc
-- title:
--   Existence of a Bruhat function for the unipotent subgroup of GL₂(A_K)
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K`, the latter equipped with a measurable space structure that is the Borel structure of its topology, and let $\mu$ be a measure on $\mathbb{A}_K$ that is an additive Haar measure. The group $\mathrm{GL}_2(\mathbb{A}_K)$ carries the Borel $\sigma$-algebra of its topology (the instance [`NumberField.AdelicHaar.glBorel`](def/NumberField_AdelicHaar.html#L176)). For $x \in \mathbb{A}_K$ write $n(x) =$ [`AutomorphicForm.unipotentGL2 x`](def/AutomorphicForm_ConstantTerm.html#L17) for the element of $\mathrm{GL}_2(\mathbb{A}_K)$ with matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and inverse matrix $\begin{pmatrix}1&-x\\0&1\end{pmatrix}$. The assertion is that there exists a function $w \colon \mathrm{GL}_2(\mathbb{A}_K) \to [0,\infty]$, with values in the extended non-negative reals, which is Borel measurable and satisfies $$\int_{\mathbb{A}_K}^{-} w\bigl(g\, n(x)\bigr)\, d\mu(x) = 1$$ for *every* $g \in \mathrm{GL}_2(\mathbb{A}_K)$, the integral being the lower Lebesgue integral of an $[0,\infty]$-valued function; the normalisation is thus required at each point $g$, not merely almost everywhere.
--
--   Such a $w$ is a Bruhat function for the closed subgroup $N = \{n(x) : x \in \mathbb{A}_K\} \cong \mathbb{A}_K$ of $\mathrm{GL}_2(\mathbb{A}_K)$, acting by right translation: it is the auxiliary datum through which integrals over the group are disassembled into an integral over $\mathrm{GL}_2(\mathbb{A}_K)/N$ followed by one along the fibres of $N$. It is used in the mirabolic decomposition of a Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, feeding the computations of the integral of a function against $g \mapsto (g e_1, \det g)$ and of the resulting Dedekind zeta factor. The proof of existence invokes second countability of $\mathbb{A}_K$ and of $\mathrm{GL}_2(\mathbb{A}_K)$ and the componentwise criterion for measurability of maps into a restricted product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure) :
    ∃ w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ≥0∞, Measurable w ∧
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1 := by sorry
