-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod
-- name    : AutomorphicForm.LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/094c37a2-6b91-5c05-9708-888b69cd4eb6
-- title:
--   Uniform bound for archimedean K-type intertwining integrals
-- statement:
--   Let $F$ be a number field, let $k$ assign an integer $k_i$ to each real place $i$ of $F$, and let $abm$ assign to each complex place $w$ a triple of natural numbers $(a_w,b_w,m_w)$ subject to $a_w+b_w\le m_w$. The assertion is the existence of a single real constant $C$ such that for every real $\sigma$ with $1/2<\sigma$ and $\sigma\le 1$ the norm of the Bochner integral, over the mixed space $\mathbb{R}^{\{w\ \text{real}\}}\times\mathbb{C}^{\{w\ \text{complex}\}}$ of $F$ equipped with its product Lebesgue measure, of the $\mathbb{C}$-valued integrand
--   $$\Big(\prod_{i\ \text{real}}\Big(\frac{x_i-\mathrm{i}}{\sqrt{1+x_i^{2}}}\Big)^{k_i}\,(1+x_i^{2})^{-(\sigma+1/2)}\Big)\cdot\Big(\prod_{w\ \text{complex}}z_w^{a_w}\,\overline{z_w}^{\,b_w}\,(1+\lVert z_w\rVert^{2})^{-(2\sigma+1)-m_w/2}\Big)$$
--   is at most $C$; here the real-place exponent $k_i$ is an integer power of the Cayley factor, the conjugation is the star ring endomorphism of $\mathbb{C}$, and the powers of the positive real quantities $1+x_i^{2}$ and $1+\lVert z_w\rVert^{2}$ are complex powers with the indicated complex exponents. The constant is independent of $\sigma$.
--
--   The integrand is the archimedean part of a pure-tensor intertwining integral for $\mathrm{GL}_2$ over $F$, with prescribed $K$-type data $k_i$ at the real places and $(a_w,b_w,m_w)$ at the complex places. The uniform bound on the strip $1/2<\sigma\le 1$ is what permits passage to the limit $\sigma\downarrow 1/2$, and it is used in [`AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family`](thm.html#AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod.lean

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace

open scoped Classical in

theorem AutomorphicForm.LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod
    (F : Type) [Field F] [NumberField F]
    (kdat : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (_habm : ∀ w, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 →
      ‖∫ y : mixedEmbedding.mixedSpace F,
          (∏ i : {w : InfinitePlace F // w.IsReal},
              ((((y.1 i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (kdat i)
                * (((1 + (y.1 i) ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2)))
          * (∏ w : {w : InfinitePlace F // w.IsComplex},
              (y.2 w) ^ (abm w).1 * (starRingEnd ℂ) (y.2 w) ^ (abm w).2.1
                * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((abm w).2.2 : ℂ) / 2))‖ ≤ C := by sorry
