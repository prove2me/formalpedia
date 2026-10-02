-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctions_l_proximity_theorem
-- name    : DiscreteConvex.LConvexFunctions.l_proximity_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:15:35.254065+00:00
-- url     : https://prove2.me/theorems/b6af0b1a-7a46-4ed3-b334-dd0529ef281d
-- title:
--   Theorem 7.18 -- the L-proximity theorem
-- statement:
--   **Theorem 7.18** (p.186). Assume $\alpha \in \mathbb Z_{++}$ and $n=|V|$. (1) Let $g$ be L-convex with $g(p)=g(p+\mathbf 1)$ for all $p$. If $p_\alpha \in \operatorname{dom} g$ satisfies $g(p_\alpha) \le g(p_\alpha + \alpha\chi_Y)$ for all $Y \subseteq V$, then $\arg\min g \ne \emptyset$ and there is $p^* \in \arg\min g$ with $p_\alpha \le p^* \le p_\alpha + (n-1)(\alpha-1)\mathbf 1$ (componentwise). (2) Let $g$ be L$^\natural$-convex. If $p_\alpha$ satisfies the same inequality for both $+\alpha\chi_Y$ and $-\alpha\chi_Y$, then $\arg\min g \ne \emptyset$ and there is $p^*$ with $p_\alpha - n(\alpha-1)\mathbf 1 \le p^* \le p_\alpha + n(\alpha-1)\mathbf 1$.
--
--   The structural mirror of chunk 06's Theorem 6.37, but the bound here is a genuine **componentwise vector inequality** using the lattice order, not an $\ell^\infty$-norm bound — this is the form the book's later applications (e.g. network duality in chapter 9) actually need, and converting it to a norm bound would silently discard the direction-of-approach information the vector form carries.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, Theorem 7.18.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, Theorem 7.18

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctions_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctions_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_LConvexFunctions_IndicatorVec

namespace DiscreteConvex.LConvexFunctions

/-- Theorem 7.18, the L-proximity theorem (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.186). Assume `α ∈ Z++` and `n = |V|`. (1) Let `g` be L-convex with `g(p) = g(p+1)` for all
`p`. If `pα ∈ dom g` satisfies `g(pα) ≤ g(pα + αχ_Y)` for all `Y ⊆ V`, then `arg min g ≠ ∅` and
there is `p* ∈ arg min g` with `pα ≤ p* ≤ pα + (n-1)(α-1)·1` (componentwise). (2) Let `g` be
L♮-convex. If `pα ∈ dom g` satisfies `g(pα) ≤ g(pα ± αχ_Y)` for all `Y ⊆ V`, then
`arg min g ≠ ∅` and there is `p* ∈ arg min g` with `pα - n(α-1)·1 ≤ p* ≤ pα + n(α-1)·1`. -/
theorem l_proximity_theorem {V : Type*} [Fintype V] [DecidableEq V] (α : ℤ) (hα : 0 < α) :
    (∀ g : (V → ℤ) → WithTop ℝ, SBF g → TRF g → (∀ p : V → ℤ, g (fun v => p v + 1) = g p) →
        ∀ pα ∈ DomZ g,
          (∀ Y : Finset V, g pα ≤ g (fun v => pα v + α * IndicatorVec Y v)) →
          (ArgMin g).Nonempty ∧ ∃ p ∈ ArgMin g, ∀ v : V,
            pα v ≤ p v ∧ p v ≤ pα v + ((Fintype.card V : ℤ) - 1) * (α - 1)) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNaturalConvex g → ∀ pα ∈ DomZ g,
        (∀ Y : Finset V, g pα ≤ g (fun v => pα v + α * IndicatorVec Y v) ∧
            g pα ≤ g (fun v => pα v - α * IndicatorVec Y v)) →
        (ArgMin g).Nonempty ∧ ∃ p ∈ ArgMin g, ∀ v : V,
          pα v - (Fintype.card V : ℤ) * (α - 1) ≤ p v ∧
            p v ≤ pα v + (Fintype.card V : ℤ) * (α - 1)) := by sorry

end DiscreteConvex.LConvexFunctions
