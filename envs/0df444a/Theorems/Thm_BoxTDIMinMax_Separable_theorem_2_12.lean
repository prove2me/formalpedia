-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_theorem_2_12
-- name    : BoxTDIMinMax.Separable.theorem_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:41.052029+00:00
-- url     : https://prove2.me/theorems/2f08a63c-1c0c-47b2-a98e-a0761cc2ee17
-- title:
--   Theorem 2.12, p. 10 — integral y∗ ≥ 0 with ℓ ≤ y∗Q ≤ u and y∗(Qz∗ − p) = 0 exists iff (2.9) holds for all pairs (2.10)
-- statement:
--   Let $Q\in\mathbb Z^{I\times S}$ and $p\in\mathbb Z^I$ with $Qx\ge p$ box-TDI, let $z^*$ be an integral element of $R=\{x\in\mathbb R^S : Qx\ge p\}$, and let $\ell:S\to\mathbb Z\cup\{-\infty\}$ and $u:S\to\mathbb Z\cup\{+\infty\}$ be integer-valued bounding vectors with $\ell\le u$. There exists an integer-valued nonnegative vector $y^*$ such that
--   $$\ell\le y^*Q\le u\qquad\text{and}\qquad y^*(Qz^*-p)=0$$
--   if and only if
--   $$\tilde\ell(S^-)\le\tilde u(S^+) \qquad (2.9)$$
--   holds for every pair $(S^-,S^+)$ of disjoint subsets of $S$ for which $z':=z^*+\chi_{S^+}-\chi_{S^-}\in R$ (2.10), where $\chi_{S^+}$, $\chi_{S^-}$ are the characteristic vectors and $\tilde\ell(X)=\sum_{s\in X}\ell(s)$.
--
--   This is the main tool of the paper: applied to the slopes of $\Phi$ at a minimizer it produces the optimal dual vector of the min-max formula (3.14).
--
--   **Formalization Note** $\ell$, $u$ are `EReal`-valued with every $\ell(s)$ either $-\infty$ or an integer and every $u(s)$ either $+\infty$ or an integer; the sums in (2.9) therefore never mix $+\infty$ and $-\infty$. Since $z'$ is integral, $z'\in R$ is written as $z'\in\ddot R$.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 10, Theorem 2.12, (2.9), (2.10)

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Theorem 2.12, p. 10: let `Q x ≥ p` (integral) be box-TDI, `z* ∈ R̈`, and
`ℓ : S → ℤ ∪ {-∞}`, `u : S → ℤ ∪ {+∞}` with `ℓ ≤ u`. There is an integral `y* ≥ 0` with
`ℓ ≤ y* Q ≤ u` and `y*(Q z* - p) = 0` if and only if `ℓ̃(S⁻) ≤ ũ(S⁺)` (2.9) for every pair of
disjoint `S⁻, S⁺ ⊆ S` with `z* + χ_{S⁺} - χ_{S⁻} ∈ R` (2.10). -/
theorem theorem_2_12 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (zStar : S → ℤ) (hz : zStar ∈ intPts Q p)
    (lo up : S → EReal)
    (hlo : ∀ s, lo s = ⊥ ∨ ∃ k : ℤ, lo s = ((k : ℝ) : EReal))
    (hup : ∀ s, up s = ⊤ ∨ ∃ k : ℤ, up s = ((k : ℝ) : EReal))
    (hlu : ∀ s, lo s ≤ up s) :
    (∃ yStar : ι → ℤ, 0 ≤ yStar ∧
        (∀ s, lo s ≤ ((((yStar ᵥ* Q) s : ℤ) : ℝ) : EReal) ∧
          ((((yStar ᵥ* Q) s : ℤ) : ℝ) : EReal) ≤ up s) ∧
        yStar ⬝ᵥ (Q *ᵥ zStar - p) = 0) ↔
      Cond29 Q p zStar lo up := by sorry

end BoxTDIMinMax.Separable
