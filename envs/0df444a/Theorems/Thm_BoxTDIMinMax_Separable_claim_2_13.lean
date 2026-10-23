-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_claim_2_13
-- name    : BoxTDIMinMax.Separable.claim_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:37.603979+00:00
-- url     : https://prove2.me/theorems/f2855c09-4a91-431c-904a-aa63061c346f
-- title:
--   Claim 2.13, p. 11 (proof of Theorem 2.12), with the columns of infinite bounds removed as on p. 11 — the LP (2.11) has optimum M = 0
-- statement:
--   Assume the hypotheses of Theorem 2.12: $Qx\ge p$ is box-TDI with $Q$, $p$ integral, $z^*\in\ddot R$, and $\ell:S\to\mathbb Z\cup\{-\infty\}$, $u:S\to\mathbb Z\cup\{+\infty\}$ satisfy $\ell\le u$. Assume moreover that $\tilde\ell(S^-)\le\tilde u(S^+)$ (2.9) for every pair of disjoint $S^-,S^+\subseteq S$ with $z^*+\chi_{S^+}-\chi_{S^-}\in R$ (2.10). Let $p_0=p-Qz^*$ and consider the linear program
--   $$M=\min\{\,u x_2-\ell x_1\ :\ (x_1,x_2)\ge 0,\ Qx_2-Qx_1\ge p_0\,\}, \qquad (2.11)$$
--   in which, as the paper prescribes, the columns of $Q$ for elements $s$ with $u(s)=+\infty$ and the columns of $-Q$ for elements $s$ with $\ell(s)=-\infty$ are removed. Then
--   $$M=0,$$
--   and the minimum is attained.
--
--   Together with the box-TDI-ness of (2.8) this gives the integral dual solution $y^*$ with $y^*(Qz^*-p)=0$ and $\ell\le y^*Q\le u$ in Theorem 2.12.
--
--   **Formalization Note** Removing a column is encoded by fixing the corresponding variable to $0$: $x_2(s)=0$ when $u(s)=+\infty$ and $x_1(s)=0$ when $\ell(s)=-\infty$. On the remaining variables the coefficients $u(s)$, $\ell(s)$ are finite integers and are read through `EReal.toReal`. The statement is that $0$ is the least element of the set of objective values of feasible real points.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 11, Claim 2.13 (in the proof of Theorem 2.12), (2.11)

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Claim 2.13, p. 11 (proof of Theorem 2.12): under the hypotheses of Theorem 2.12 and (2.9) for
every pair (2.10), the linear program (2.11)
`min {u x₂ - ℓ x₁ : (x₁, x₂) ≥ 0, Q x₂ - Q x₁ ≥ p₀}`, `p₀ = p - Q z*`, in which (as on p. 11)
the columns of `Q` with `u(s) = +∞` and those of `-Q` with `ℓ(s) = -∞` are removed (the
corresponding variables are fixed to `0`), has optimum value `M = 0`, attained. -/
theorem claim_2_13 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (zStar : S → ℤ) (hz : zStar ∈ intPts Q p)
    (lo up : S → EReal)
    (hlo : ∀ s, lo s = ⊥ ∨ ∃ k : ℤ, lo s = ((k : ℝ) : EReal))
    (hup : ∀ s, up s = ⊤ ∨ ∃ k : ℤ, up s = ((k : ℝ) : EReal))
    (hlu : ∀ s, lo s ≤ up s)
    (h29 : Cond29 Q p zStar lo up) :
    IsLeast {v : ℝ | ∃ x₁ x₂ : S → ℝ, 0 ≤ x₁ ∧ 0 ≤ x₂ ∧
        (∀ s, lo s = ⊥ → x₁ s = 0) ∧ (∀ s, up s = ⊤ → x₂ s = 0) ∧
        (∀ i, (((p - Q *ᵥ zStar) i : ℤ) : ℝ) ≤
          ∑ s, (Q i s : ℝ) * x₂ s - ∑ s, (Q i s : ℝ) * x₁ s) ∧
        v = ∑ s, (up s).toReal * x₂ s - ∑ s, (lo s).toReal * x₁ s} 0 := by sorry

end BoxTDIMinMax.Separable
