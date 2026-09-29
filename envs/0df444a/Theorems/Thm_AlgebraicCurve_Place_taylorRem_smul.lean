-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_taylorRem_smul
-- name    : AlgebraicCurve.Place.taylorRem_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/173a5ec8-9e46-5f57-bac1-d705877d07e2
-- title:
--   Taylor remainders at a rational place are K-homogeneous
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal O_v =$ `v.toValuationSubring` of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, meaning that the induced map from $K$ to the residue field $\mathcal O_v/\mathfrak m_v$ is surjective. Let $t \in F$ satisfy $\operatorname{ord}_v t = 1$, where $\operatorname{ord}_v$ is minus the logarithm of the associated $\mathbb Z^{m0}$-valued adic valuation, and let $f \in \mathcal O_v$. Fix $c \in K$ and $r \in \mathbb N$. The Taylor remainders along $t$ are defined recursively by $\rho_0(g) = g$ and $\rho_{r+1}(g) = \bigl(\rho_r(g) - \iota(v.\mathrm{evalAt}\,\rho_r(g))\bigr)t^{-1}$, where $\iota : K \to F$ is the structure map and $v.\mathrm{evalAt}$ sends an element of $\mathcal O_v$ to the element of $K$ representing its residue (and everything outside $\mathcal O_v$ to $0$). The assertion is the identity $\rho_r(c \cdot f) = c \cdot \rho_r(f)$ for the $K$-scalar action on $F$.
--
--   This is the homogeneity half of the $K$-linearity of the Taylor remainder operators $\rho_r$ attached to a rational place and a uniformiser; together with the corresponding additivity statement it makes $f \mapsto \rho_r(f)$ a $K$-linear map on the local ring $\mathcal O_v$. It is used to derive the analogous homogeneity of the Taylor coefficients, [`AlgebraicCurve.Place.taylorCoeff_smul`](thm.html#AlgebraicCurve.Place.taylorCoeff_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_taylorRem_smul.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorRem_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) (r : ℕ) :
    taylorRem v t (c • f) r = c • taylorRem v t f r := by sorry
