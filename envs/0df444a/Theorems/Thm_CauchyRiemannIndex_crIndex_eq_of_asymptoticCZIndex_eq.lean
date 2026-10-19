-- Prove2me | Theorems.Thm_CauchyRiemannIndex_crIndex_eq_of_asymptoticCZIndex_eq
-- name    : CauchyRiemannIndex.crIndex_eq_of_asymptoticCZIndex_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:50:32.259228+00:00
-- url     : https://prove2.me/theorems/721ec9eb-3e1f-40f2-8f10-001901cffbbf
-- title:
--   The Fredholm index of a Cauchy–Riemann operator on the cylinder depends only on its asymptotic Conley–Zehnder indices
-- statement:
--   Let $1<p<\infty$ and $n\ge0$. Let $S,T:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous coefficients with $S(s,\cdot)\to S^\pm$ and $T(s,\cdot)\to T^\pm$ uniformly as $s\to\pm\infty$, where $S^\pm,T^\pm$ are continuous loops of symmetric matrices whose asymptotic operators $-J_0\partial_t-S^\pm$ and $-J_0\partial_t-T^\pm$ are nondegenerate. If
--   $$\mu_{CZ}(-J_0\partial_t-S^+)=\mu_{CZ}(-J_0\partial_t-T^+),\qquad \mu_{CZ}(-J_0\partial_t-S^-)=\mu_{CZ}(-J_0\partial_t-T^-),$$
--   then the Cauchy–Riemann operators $D_S,D_T:W^{1,p}(\mathbb{R}\times S^1,\mathbb{R}^{2n})\to L^p(\mathbb{R}\times S^1,\mathbb{R}^{2n})$ have the same Fredholm index: $\operatorname{ind}D_S=\operatorname{ind}D_T$.
--
--   This says the index on the cylinder depends only on the Conley–Zehnder indices at the two ends. It is used to compute indices by comparing with any convenient operator that has the same asymptotic indices.
--
--   **Formalization Note** $D_S=\partial_s+J_0\partial_t+S$; the index is `crIndex p S` $=\dim\ker D_S-\dim\operatorname{coker}D_S$ from the setting module. Loops are continuous $1$-periodic maps $\mathbb{R}\to\mathbb{R}^{2n\times2n}$ (`IsSymLoop`), nondegeneracy is `IsNondegenerate` (no eigenvalue $1$ of the time-one map of $\Psi'=J_0S^\pm\Psi$), and the Conley–Zehnder index is `asymptoticCZIndex`. The asymptotic convergence is `IsAsymptoticTo S Splus Sminus` (positive end first).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, §5.8, pp. 102-103 (cylinder, trivial bundle)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lecture 5 (§ 5.8, p. 103), on the cylinder with the trivial bundle and `1 < p < ∞`: the
Fredholm index of `D_S : W^{1,p} → L^p` depends only on the Conley–Zehnder indices of its
asymptotic operators. If `D_S` is asymptotic to nondegenerate loops `S±` and `D_T` to
nondegenerate loops `T±` with `μ_CZ(-J₀ ∂ₜ - S±) = μ_CZ(-J₀ ∂ₜ - T±)`, then
`ind D_S = ind D_T`. -/
theorem crIndex_eq_of_asymptoticCZIndex_eq (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Splus Sminus Tplus Tminus : ℝ → Mat n)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (hTplus : IsSymLoop Tplus) (hTminus : IsSymLoop Tminus)
    (hnSplus : IsNondegenerate Splus) (hnSminus : IsNondegenerate Sminus)
    (hnTplus : IsNondegenerate Tplus) (hnTminus : IsNondegenerate Tminus)
    (hμplus : asymptoticCZIndex Splus = asymptoticCZIndex Tplus)
    (hμminus : asymptoticCZIndex Sminus = asymptoticCZIndex Tminus)
    (S T : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus)
    (hT : IsAsymptoticTo T Tplus Tminus) :
    crIndex p S = crIndex p T := by
  sorry

end CauchyRiemannIndex
