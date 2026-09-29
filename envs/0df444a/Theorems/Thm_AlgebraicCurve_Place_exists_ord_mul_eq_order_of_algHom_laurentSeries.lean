-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries
-- name    : AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/a09cc34f-f4eb-5951-b5ff-76663dc0215e
-- title:
--   Places from K-algebra embeddings into Laurent series
-- statement:
--   Let $K$ be a field, $F$ a field equipped with a $K$-algebra structure, and $\iota : F \to K((T))$ a $K$-algebra homomorphism into the Laurent series field over $K$ (Hahn series with value group $\mathbb{Z}$). Assume the non-triviality hypothesis that some $x \in F$ has $\mathrm{order}(\iota x) \neq 0$, i.e. the $T$-adic order pulled back along $\iota$ is not identically zero. The conclusion asserts the existence of a place $w$ of $F$ over $K$ — that is, a valuation subring of $F$ which contains $\mathrm{algebraMap}\,K\,F(a)$ for every $a \in K$, is not all of $F$, and is a principal ideal ring — together with a natural number $\gamma$ with $0 < \gamma$, such that for every $x \in F$ one has $\mathrm{ord}_w(x)\cdot\gamma = \mathrm{order}(\iota x)$ in $\mathbb{Z}$, where $\mathrm{ord}_w(x)$ is minus the logarithm of the value of $x$ under the height-one-spectrum adic valuation attached to $w$. Thus the $T$-adic order of $\iota$ is a positive integral multiple of a normalised discrete valuation of $F$ trivial on $K$; $\gamma$ plays the role of the ramification index of the embedding.
--
--   This is the standard device by which an analytic (Laurent-series) expansion of a function field determines a place of that field over the base field, with the expansion order equal to the valuation up to a positive integer factor. It is used to produce places of function fields of modular curves and of their base changes to Laurent series, and is cited in the analysis of orders of $j$ and of cusp counting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (ι : F →ₐ[K] LaurentSeries K)
    (h : ∃ x : F, (ι x).order ≠ 0) :
    ∃ (w : Place K F) (γ : ℕ), 0 < γ ∧ ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order := by sorry
