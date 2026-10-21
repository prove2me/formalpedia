-- Prove2me | Theorems.Thm_CauchyRiemannIndex_isAsymptoticTo_diamond
-- name    : CauchyRiemannIndex.isAsymptoticTo_diamond
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T15:43:42.489521+00:00
-- url     : https://prove2.me/theorems/d9f4c077-a4de-4ac6-9aa1-7f16d14297ef
-- title:
--   Block-diagonal sums of asymptotic coefficients on the cylinder are asymptotic to the block-diagonal sums of the limits
-- statement:
--   Let $S_1:\mathbb{R}\times\mathbb{R}\to\mathbb{R}^{2m_1\times2m_1}$ be continuous, $1$-periodic in the second variable, with $S_1(s,t)\to A^\pm(t)$ as $s\to\pm\infty$ uniformly in $t$ (entrywise), and let $S_2:\mathbb{R}\times\mathbb{R}\to\mathbb{R}^{2m_2\times2m_2}$ be likewise asymptotic to $B^\pm$. Then the block-diagonal coefficient $S_1\diamond S_2$ on $\mathbb{R}^{2m_1}\oplus\mathbb{R}^{2m_2}$, with $(q',p')\oplus(q'',p'')\mapsto(q',q'',p',p'')$, is continuous, $1$-periodic in the second variable, and asymptotic to $A^+\diamond B^+$ as $s\to+\infty$ and to $A^-\diamond B^-$ as $s\to-\infty$.
--
--   This lets block-diagonal Cauchy–Riemann operators on the cylinder be used with the results stated for asymptotic coefficients.
--
--   **Formalization Note** The block-diagonal sum is `ConleyZehnder.diamond`, applied pointwise. Asymptotic convergence is `IsAsymptoticTo S Splus Sminus` from the setting module (positive end first).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Definition 4.2 (asymptotic coefficients), applied to direct sums

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- If `S₁` is asymptotic to `A₊, A₋` and `S₂` is asymptotic to `B₊, B₋`, then the block-diagonal
coefficient `S₁ ⋄ S₂` is asymptotic to `A₊ ⋄ B₊, A₋ ⋄ B₋`. -/
theorem isAsymptoticTo_diamond {m₁ m₂ : ℕ} (S₁ : ℝ × ℝ → Mat m₁) (S₂ : ℝ × ℝ → Mat m₂)
    (Ap Am : ℝ → Mat m₁) (Bp Bm : ℝ → Mat m₂) (h₁ : IsAsymptoticTo S₁ Ap Am)
    (h₂ : IsAsymptoticTo S₂ Bp Bm) :
    IsAsymptoticTo (fun x => ConleyZehnder.diamond (S₁ x) (S₂ x))
      (fun t => ConleyZehnder.diamond (Ap t) (Bp t))
      (fun t => ConleyZehnder.diamond (Am t) (Bm t)) := by
  sorry

end CauchyRiemannIndex
