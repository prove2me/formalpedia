-- Prove2me | Theorems.Thm_AssortOpt_HMF_Supplement_theorem_5
-- name    : AssortOpt.HMF.Supplement.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:23:33.081492+00:00
-- url     : https://prove2.me/theorems/e4446368-43bc-4fb1-aa1d-e71d32bc189f
-- title:
--   Theorem 5 — capped independent inclusion earns at least 2/(eL) of every IC mechanism
-- statement:
--   Let $D$ be a finite list distribution with nonnegative fixed prices $r_j$, and let $x$ satisfy the IC constraints (3)–(5) on its report domain $R$, which contains the positive support of $D$. Set $L=\max_{\ell:p(\ell)>0}|\ell|$ and $f_j=\max_{\ell\in R:j\in\ell}x_j(\ell)$, with $f_j=0$ for an unavailable item. For $L>0$, independently include item $j$ with probability $\varphi(f_j)$, where
--   $$\varphi(a)=\begin{cases}2a/L,&a\le1/2,\\1/L,&a>1/2.\end{cases}\qquad
--   \mathbb E_S[\mathsf{REV}[S]]\ge\frac{2}{eL}\mathsf{REV}[x].$$
--   The statement includes $L=1$. When $L=0$, all realizable lists are empty; offering nothing gives zero assortment revenue and the mechanism revenue is zero. The Lean statement explicitly asserts these equalities and uses a zero coefficient in that case.
--
--   This companion theorem bounds the loss from assortments for every IC mechanism using only the maximum realizable list length. No all-list report domain or positive revenue assumption is added.
--
--   Differences from the source:
--   - encoding: items N={1,…,n} and a finite list distribution → 0-based Fin n and the published ListDist with strictly positive support of Nodup lists; reason: the same finite distributions, including empty lists and n=0, are represented
--   - encoding: the report domain ℒ, possibly containing probability-zero types → a finite Nodup report domain R containing the positive support, with constraints (3)–(5) in IsICOn; reason: constraints and allocation maxima read all reports while the objective and maximum realizable length read only positive-mass types
--   - encoding: maxima over reports, including the item-allocation maxima fⱼ → attained finite maxima with zero adjoined, and zero for an item never appearing in the domain; reason: IC makes every relevant allocation nonnegative, so adjoining zero does not change a nonempty maximum
--   - encoding: ϕ(a) and 2/(eL) are undefined at L=0 → zero inclusion probabilities and zero approximation coefficient at L=0, with both revenues explicitly zero; reason: L=0 means every positive-mass list is empty; this boundary convention excludes no source instance and avoids using division by zero as a probability rule
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 25, Theorem 5

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_BudgetRandom

namespace AssortOpt.HMF.Supplement

theorem theorem_5 {n : ℕ} (D : ListDist n) (R : Finset (List (Fin n)))
    (hR : ∀ ℓ ∈ R, ℓ.Nodup) (hsupp : D.supp ⊆ R)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (x : List (Fin n) → Fin n → ℝ) (hx : IsICOn R x) :
    (maxLength D = 0 →
      revMech D r x = 0 ∧
        revIndependent D r (fun j => cappedInclusion (maxLength D) (maxAlloc R x j)) = 0) ∧
    lengthFactor (maxLength D) * revMech D r x ≤
      revIndependent D r (fun j => cappedInclusion (maxLength D) (maxAlloc R x j)) := by sorry

end AssortOpt.HMF.Supplement
