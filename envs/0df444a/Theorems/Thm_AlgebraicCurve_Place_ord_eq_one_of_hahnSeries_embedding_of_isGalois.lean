-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_eq_one_of_hahnSeries_embedding_of_isGalois
-- name    : AlgebraicCurve.Place.ord_eq_one_of_hahnSeries_embedding_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e6750ed9-f48c-5d21-988d-2c0753c3ebc9
-- title:
--   Laurent embedding over a simple root forces ord_W p = 1
-- statement:
--   Let $K \subseteq L$ be fields ($L$ a $K$-algebra), and let $M$ be a field that is an algebra over $K$ and over the rational function field $\mathrm{RatFunc}\,K$, compatibly (scalar tower $K \to \mathrm{RatFunc}\,K \to M$), with $M/\mathrm{RatFunc}\,K$ finite-dimensional and Galois. Let $p \in K[X]$ be irreducible and let $a \in L$ satisfy $p(a) = 0$ and $p'(a) \neq 0$, i.e. $a$ is a simple root of $p$ in $L$. Let $\psi : M \to \mathrm{HahnSeries}\,\mathbb{Q}\,L$ be a $K$-algebra homomorphism into the Hahn series field over $L$ with value group $\mathbb{Q}$ such that the image of $X$ (pushed from $K[X]$ through $\mathrm{RatFunc}\,K$ into $M$) is the series $a + t$, namely the constant series $a$ plus the monomial $1 \cdot t^{1}$, and such that every $\psi(m)$ satisfies $\mathrm{HasRamBound}\,1$, that is, its support is contained in the image of $\mathbb{Z} \to \mathbb{Q}$, $k \mapsto k/1$; so $\psi$ lands in Laurent series. Finally let $W$ be a place of $M$ over $K$, given by a valuation subring of $M$ that contains the image of $K$, is not all of $M$, and is a principal ideal ring, and write $W.\mathrm{ord}$ for the associated additive valuation (minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation of $W$). If $W.\mathrm{ord}$ of the image of $p$ in $M$ is positive, then it equals $1$.
--
--   In classical terms: a place of $M$ lying over the closed point of the affine line cut out by $p$ is unramified, the Laurent-series embedding sending $X$ to $a + t$ at a simple root $a$ of $p$ exhibiting one such place as unramified and the Galois action transferring this to the whole fibre. The result feeds into [`AlgebraicCurve.Place.ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one`](thm.html#AlgebraicCurve.Place.ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_eq_one_of_hahnSeries_embedding_of_isGalois.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ord_eq_one_of_hahnSeries_embedding_of_isGalois
    {K L M : Type*} [Field K] [Field L] [Algebra K L] [Field M] [Algebra K M]
    [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
    [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]
    (p : Polynomial K) (hp : Irreducible p) (a : L)
    (ha : Polynomial.aeval a p = 0) (ha' : Polynomial.aeval a (Polynomial.derivative p) ≠ 0)
    (ψ : M →ₐ[K] HahnSeries ℚ L)
    (hψX : ψ (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
      = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L))
    (hψ : ∀ m : M, HahnSeries.HasRamBound 1 (ψ m))
    (W : AlgebraicCurve.Place K M)
    (hW : 0 < W.ord (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p))) :
    W.ord (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p)) = 1 := by sorry
