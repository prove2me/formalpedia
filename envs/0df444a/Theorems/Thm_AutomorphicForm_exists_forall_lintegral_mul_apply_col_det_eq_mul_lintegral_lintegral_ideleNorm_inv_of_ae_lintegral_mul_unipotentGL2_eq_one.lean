-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one
-- name    : AutomorphicForm.exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/c28bd153-bfc7-5ba6-8305-d0d3e9909e76
-- title:
--   Weil integration formula on GL₂(A_K) along unipotent fibres
-- statement:
--   Let $K$ be a number field, with its adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K` and unit group $\mathbb{A}_K^\times$ each carrying a measurable structure that is the Borel structure of its topology, and with $\mathrm{GL}_2(\mathbb{A}_K)$ carrying the Borel $\sigma$-algebra (the local instance `glBorel`). Let $\tau$ be a Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, $\mu$ an additive Haar measure on $\mathbb{A}_K$, and $\nu$ a Haar measure on $\mathbb{A}_K^\times$. The assertion is the existence of a constant $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$ such that for every measurable $w \colon \mathrm{GL}_2(\mathbb{A}_K) \to [0,\infty]$ and every measurable $\Psi \colon \mathbb{A}_K^2 \times \mathbb{A}_K^\times \to [0,\infty]$, if $\int_{\mathbb{A}_K} w\bigl(g\,n(x)\bigr)\,d\mu(x) = 1$ for $\tau$-almost every $g$, where $n(x) = \bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)$ is [`AutomorphicForm.unipotentGL2 x`](def/AutomorphicForm_ConstantTerm.html#L17), then $$\int_{\mathrm{GL}_2(\mathbb{A}_K)} w(g)\,\Psi\bigl((g_{i0})_{i},\ \det g\bigr)\,d\tau(g) = c \int_{\mathbb{A}_K^2}\!\int_{\mathbb{A}_K^\times} \Psi(p,\delta)\,\lVert\delta\rVert^{-1}\,d\nu(\delta)\,d\mu^{\otimes 2}(p),$$ the outer measure being the product measure $\mu^{\otimes 2}$ on $\mathbb{A}_K^2$, the first argument of $\Psi$ on the left being the first column of $g$, and $\lVert\delta\rVert$ denoting [`NumberField.TateGlobal.ideleNorm K δ`](def/NumberField_TateGlobalZeta.html#L19), the value at $\delta$ of the distributive Haar character of the scaling action on $\mathbb{A}_K$, with $\lVert\delta\rVert^{-1}$ inverted in $\mathbb{R}$ and then mapped into $[0,\infty]$. The constant $c$ depends only on $\tau$, $\mu$, $\nu$ and is uniform in $w$ and $\Psi$.
--
--   This is Weil's integration formula $\int_G = \int_{G/N}\int_N$ for $G = \mathrm{GL}_2(\mathbb{A}_K)$ and the unipotent group $N = \{n(x)\}$ stabilising the first basis vector, in qualitative form: the pushforward of $\tau$ under $g \mapsto (ge_1, \det g)$, after cutting the $N$-fibres by a weight $w$ of total mass one, is the measure $\lVert\delta\rVert^{-1}\,d\nu(\delta)\,d\mu^{\otimes 2}(p)$ up to a finite nonzero factor independent of the weight. It feeds the computation, for the standard normalisations, of the constant as a product involving $\zeta_K(2)$ in the subsequent evaluation of the global zeta integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure)
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ≥0∞)
        (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞),
        Measurable w → Measurable Ψ →
        (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
          c * ∫⁻ p, ∫⁻ δ, Ψ (p, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
            ∂(Measure.pi fun _ : Fin 2 => μ) := by sorry
