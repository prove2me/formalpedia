-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_dvd_of_hahnSeries_embedding_of_isGalois
-- name    : AlgebraicCurve.Place.ord_dvd_of_hahnSeries_embedding_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/6246ce2f-6eb6-5afc-ad64-e8999f7315b9
-- title:
--   Puiseux bound d forces ord_W(p)∣ d
-- statement:
--   Let $K\subseteq L$ be fields ($L$ a $K$-algebra), and let $M$ be a field that is simultaneously a $K$-algebra and an algebra over the rational function field $\mathrm{RatFunc}\,K$, the two structures being compatible (scalar tower $K\subseteq \mathrm{RatFunc}\,K\subseteq M$), with $M$ finite-dimensional and Galois over $\mathrm{RatFunc}\,K$. Let $p\in K[X]$ be irreducible and let $a\in L$ satisfy $p(a)=0$ and $p'(a)\neq 0$, i.e. $a$ is a simple root of $p$ in $L$. Let $\psi\colon M\to \mathrm{HahnSeries}\,\mathbb{Q}\,L$ be a $K$-algebra homomorphism into the Hahn series field with value group $\mathbb{Q}$ and coefficients in $L$, such that $\psi$ sends the image of $X$ in $M$ to $a+t$, that is to the constant series $a$ plus the monomial with exponent $1$ and coefficient $1$. Let $d$ be a positive natural number and assume that for every $m\in M$ the series $\psi(m)$ has $\mathrm{HasRamBound}\ d$, i.e. its support is contained in $\{k/d : k\in\mathbb{Z}\}$. Finally, let $W$ be a place of $M$ over $K$ — a valuation subring of $M$ containing $\mathrm{algebraMap}\,K\,M(K)$, different from $M$ itself, and a principal ideal ring — and write $\mathrm{ord}_W$ for the associated $\mathbb{Z}$-valued order function, minus the logarithm of the adic valuation attached to the height-one prime of $W$. Assume $\mathrm{ord}_W$ of the image of $p$ in $M$ is strictly positive, i.e. $W$ lies over the place $(p)$ of $K(X)$. Then $\mathrm{ord}_W$ of the image of $p$ divides $d$ in $\mathbb{Z}$.
--
--   This is the divisibility form of the classical statement that Puiseux expansions with denominators dividing $d$ bound the ramification: every place of $M$ above the closed point $(p)$ of the rational function field has ramification index dividing $d$, the case $d=1$ being the Laurent-series criterion for unramifiedness. It is used by [`AlgebraicCurve.Place.ord_dvd_of_forall_hahnSeries_embedding_hasRamBound`](thm.html#AlgebraicCurve.Place.ord_dvd_of_forall_hahnSeries_embedding_hasRamBound).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_dvd_of_hahnSeries_embedding_of_isGalois.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ord_dvd_of_hahnSeries_embedding_of_isGalois
    {K L M : Type*} [Field K] [Field L] [Algebra K L] [Field M] [Algebra K M]
    [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
    [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]
    (p : Polynomial K) (hp : Irreducible p) (a : L)
    (ha : Polynomial.aeval a p = 0) (ha' : Polynomial.aeval a (Polynomial.derivative p) ≠ 0)
    (ψ : M →ₐ[K] HahnSeries ℚ L)
    (hψX : ψ (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
      = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L))
    {d : ℕ} (hd : 0 < d) (hψ : ∀ m : M, HahnSeries.HasRamBound d (ψ m))
    (W : AlgebraicCurve.Place K M)
    (hW : 0 < W.ord (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p))) :
    W.ord (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p)) ∣ (d : ℤ) := by sorry
