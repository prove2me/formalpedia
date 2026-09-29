-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_smul
-- name    : AlgebraicCurve.Place.taylorCoeff_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/574cc210-ce31-516e-8700-cf536a4c4788
-- title:
--   Homogeneity of Taylor coefficients at a rational place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project, i.e. a valuation subring $\mathcal O_v \subseteq F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, meaning that the induced map from $K$ to the residue field $\mathcal O_v/\mathfrak m_v$ is surjective. Let $t \in F$ satisfy $\operatorname{ord}_v t = 1$, where $\operatorname{ord}_v$ is minus the logarithm of the associated adic valuation, so $t$ is a uniformiser at $v$. Let $f \in \mathcal O_v$, let $c \in K$ and let $r$ be a natural number. Recall the Taylor remainders, defined by $\rho_0(f) = f$ and $\rho_{s+1}(f) = (\rho_s(f) - \rho_s(f)(v))\,t^{-1}$, where $g \mapsto g(v)$ denotes the element of $K$ obtained from the residue of $g$ when $g \in \mathcal O_v$ (and $0$ otherwise), and the $r$-th Taylor coefficient $a_r(f) = \rho_r(f)(v) \in K$. The assertion is that $a_r(c \cdot f) = c\, a_r(f)$.
--
--   This is the homogeneity half of the $K$-linearity of the jet map $f \mapsto (a_0(f), \dots, a_{n-1}(f))$ on the local ring at a rational place, along a chosen uniformiser. It is used together with multiplicativity statements about Taylor coefficients in the analysis of jet matrices and Riemann–Roch spaces, and in the construction of local charts on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_taylorCoeff_smul.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorCoeff_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) (r : ℕ) :
    taylorCoeff v t r (c • f) = c * taylorCoeff v t r f := by sorry
