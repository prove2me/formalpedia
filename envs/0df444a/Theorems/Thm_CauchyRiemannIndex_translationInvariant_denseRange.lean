-- Prove2me | Theorems.Thm_CauchyRiemannIndex_translationInvariant_denseRange
-- name    : CauchyRiemannIndex.translationInvariant_denseRange
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T21:53:08.920776+00:00
-- url     : https://prove2.me/theorems/e826490d-b095-4606-b140-f8066b12f25f
-- title:
--   Translation-invariant Cauchy–Riemann operators with nondegenerate asymptotics have dense range on test sections
-- statement:
--   Let $1<p<\infty$ and let $S_\infty$ be a continuous loop of symmetric $2n\times2n$ matrices whose asymptotic operator $-J_0\partial_t-S_\infty(t)$ is nondegenerate. Then the set
--   $$\{\partial_s u+J_0\partial_t u+S_\infty(t)u\ :\ u\in C^\infty(\mathbb R\times S^1,\mathbb R^{2n}) \text{ vanishing for large } |s|\}$$
--   is dense in $L^p(\mathbb R\times S^1,\mathbb R^{2n})$: for every $f\in L^p$ and $\varepsilon>0$ there is such a $u$ with $\|\partial_su+J_0\partial_tu+S_\infty u-f\|_{L^p}<\varepsilon$.
--
--   This is the existence half of the statement that the translation-invariant operator $\partial_s+J_0\partial_t+S_\infty(t):W^{1,p}\to L^p$ is an isomorphism (Wendl, Theorem 4.11, case $k=1$).
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and $L^p(\mathbb R\times S^1)$ is `LpCyl n p`, i.e. $L^p$ of the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$). The operator is `crOp` with $S(s,t)=S_\infty(t)$, and the distance is `eLpNorm (crOp S u - f) p cylMeasure < ENNReal.ofReal ε`. Nondegeneracy is `IsNondegenerate` ($\det(1-\Psi(1))\ne0$ for the fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$). $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$, $p\ne\infty$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For `1 < p < ∞` and a nondegenerate loop `S∞` of symmetric matrices, the images
`D u = ∂ₛu + J₀ ∂ₜu + S∞(t) u` of the test sections `u` are dense in `L^p(ℝ × S¹, ℝ²ⁿ)`. -/
theorem translationInvariant_denseRange (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf)
    (f : LpCyl n p) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℝ × ℝ → Vec n, IsTestSection u ∧
      eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u - ⇑f) p cylMeasure < ENNReal.ofReal ε := by
  sorry

end CauchyRiemannIndex
