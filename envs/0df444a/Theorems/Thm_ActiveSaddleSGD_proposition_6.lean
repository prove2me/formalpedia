-- Prove2me | Theorems.Thm_ActiveSaddleSGD_proposition_6
-- name    : ActiveSaddleSGD.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:06.279323+00:00
-- url     : https://prove2.me/theorems/76f67852-7aea-4b70-8ec4-40ac37ca2be6
-- title:
--   Proposition 6 — center-stable invariant manifold (Kelley)
-- statement:
--   Consider the ODE (20) with $J^+$, $J^-$, $R$ as above. There are a neighbourhood $\mathcal U$ of $0$ in $\mathbb R^{d^+}$ and a $C^2$ function $G:\mathcal U\to\mathbb R^{d^-}$ such that:
--
--   1. $G(0)=0$ and $J_G(0)=0$;
--   2. the set $\mathcal V=\{(y^+,y^-):y^+\in\mathcal U,\ y^-=G(y^+)\}$ is invariant for (20): if $\mathrm y(t)$ is any solution starting at $\mathcal V$, there is $t_0>0$ such that $\mathrm y(t)\in\mathcal V$ for $t\in(-t_0,t_0)$.
--
--   This classical theorem provides the set from which the iterates are repelled.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ in the basis of $P$ → $\mathbb R^{d^+}\times\mathbb R^{d^-}$ with the product norm; reason: only neighbourhoods are used; same instances
--   - encoding: a neighbourhood $\mathcal U$; "any solution" → $\mathcal U$ open; a solution on an interval $(-a,a)$, $a>0$; reason: an open neighbourhood can be taken inside any neighbourhood, and solutions are local; same content
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Proposition 6, p.25, with (20)

import Mathlib
import Definitions.Def_ActiveSaddleSGD_CenterStable

namespace ActiveSaddleSGD

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Proposition 6, p.25 ([26, Theorem 1], Kelley):
for the ODE (20) there are a neighbourhood `𝒰` of `0` in `ℝ^{d⁺}` and a `C²` function
`G : 𝒰 → ℝ^{d⁻}` with `G(0) = 0`, `J_G(0) = 0`, whose graph is invariant for (20).

**Formalization Note** See `IsCenterStableGraph`. `𝒰` is taken open, which loses nothing. -/
theorem proposition_6 {dp dm : ℕ} (Jp : Matrix (Fin dp) (Fin dp) ℝ)
    (Jm : Matrix (Fin dm) (Fin dm) ℝ)
    (R : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) →
      EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm))
    (hsys : IsBlockSystem Jp Jm R) :
    ∃ (𝒰 : Set (EuclideanSpace ℝ (Fin dp)))
      (G : EuclideanSpace ℝ (Fin dp) → EuclideanSpace ℝ (Fin dm)),
      IsCenterStableGraph Jp Jm R 𝒰 G := by sorry

end ActiveSaddleSGD
