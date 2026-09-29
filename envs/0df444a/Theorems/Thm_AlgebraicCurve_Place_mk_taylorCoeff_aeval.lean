-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_mk_taylorCoeff_aeval
-- name    : AlgebraicCurve.Place.mk_taylorCoeff_aeval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/8d84e529-56c6-5feb-b21c-eae2ad982644
-- title:
--   Taylor expansion commutes with multivariate polynomial expressions
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, that is, a valuation subring $\mathcal O_v \subseteq F$ containing $\operatorname{im}(K \to F)$, different from $F$, and a principal ideal ring. Assume $v$ is rational, meaning that the induced map $K \to \mathcal O_v/\mathfrak m_v$ to the residue field is surjective, and let $t \in F$ satisfy $\operatorname{ord}_v t = 1$, the order being $-\log$ of the associated height-one-spectrum valuation. Let $\sigma$ be an index type and $f : \sigma \to F$ a family with $f_s \in \mathcal O_v$ for every $s$. For $g \in F$ write $a_n(g) = \operatorname{evalAt}_v(\operatorname{taylorRem}_v(t,g,n)) \in K$ for the $n$-th Taylor coefficient along $t$, where the remainders are given by $\operatorname{taylorRem}_v(t,g,0) = g$ and $\operatorname{taylorRem}_v(t,g,r+1) = (\operatorname{taylorRem}_v(t,g,r) - \operatorname{evalAt}_v(\operatorname{taylorRem}_v(t,g,r)))\,t^{-1}$, and $\operatorname{evalAt}_v$ sends an element of $\mathcal O_v$ to the unique preimage in $K$ of its residue and everything outside $\mathcal O_v$ to $0$. The assertion is that for every $H \in K[(X_s)_{s \in \sigma}]$ the power series $\sum_n a_n\bigl(H(f)\bigr) T^n$ in $K[[T]]$ equals the image of $H$ under the $K$-algebra map $K[(X_s)_s] \to K[[T]]$ sending $X_s$ to $\sum_n a_n(f_s) T^n$.
--
--   This says that the Taylor-expansion map $g \mapsto \sum_n a_n(g)T^n$ on the valuation ring at a rational place with uniformiser $t$ is a $K$-algebra homomorphism to $K[[T]]$, in the form of compatibility with arbitrary multivariate polynomial expressions; it is the many-variable counterpart of the bivariate statement [`AlgebraicCurve.Place.mk_taylorCoeff_evalEval`](thm.html#AlgebraicCurve.Place.mk_taylorCoeff_evalEval). It is used in the construction of formal branches through a point of a model of a modular curve, namely in the study of prolongation tuples, where jets of polynomial relations among the coordinates and the invertibility of a Jacobian determinant at the centre are computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mk_taylorCoeff_aeval.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.mk_taylorCoeff_aeval {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {σ : Type*} (f : σ → F) (hf : ∀ s, f s ∈ v.toValuationSubring) (H : MvPolynomial σ K) :
    (PowerSeries.mk fun n => taylorCoeff v t n (MvPolynomial.aeval f H))
      = MvPolynomial.aeval (fun s => PowerSeries.mk fun n => taylorCoeff v t n (f s)) H := by sorry
