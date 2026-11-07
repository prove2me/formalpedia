-- Prove2me | Theorems.Thm_BorderD4_proposition_4_13
-- name    : BorderD4.proposition_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:34.265941+00:00
-- url     : https://prove2.me/theorems/b4a2c305-15e4-479d-bc58-80323e096355
-- title:
--   Proposition 4.13: the resultant of $f$ and $\partial_z f$
-- statement:
--   Let $L$ be a field of characteristic $0$, $R=L[x]$, and $f\in R[z]$ irreducible with $d=\deg_z f\ge 1$ and $\deg_{x,z}f\le D$. Then:
--
--   1. $\mathrm{Res}_z(f,\partial_z f)\ne 0$ and $\deg\mathrm{Res}_z(f,\partial_z f)\le D(D-1)$;
--   2. if $(c,\gamma)\in L^N\times L$ satisfies $f(c,\gamma)=0$ and $\mathrm{Res}_z(f,\partial_z f)(c)\ne 0$, then $(\partial_z f)(c,\gamma)\ne 0$;
--   3. if $\ell$ is the leading coefficient of $f$ in $z$ and $\mathrm{Res}_z(f,\partial_z f)(c)\ne 0$, then $\ell(c)\ne 0$, and so $\deg_z f(c,z)=\deg_z f$.
--
--   The degree bound is what bounds the polynomial $R$ avoided by the low-weight point.
--
--   Differences from the source:
--   - encoding: the variables $x_1,\dots,x_N$ → an arbitrary finite nonempty index type; reason: any such type is $[N]$ up to renaming
--   - encoding: $\mathrm{Res}_z$ by the Sylvester matrix of Definition 4.11 → Mathlib's `Polynomial.resultant`; reason: the determinants agree up to a sign, and each clause is insensitive to it
--   - encoding: $\deg_{x,z}f\le D$ → $\deg_x(\mathrm{coeff}_i f)+i\le D$ for every $i$ in the support of $f$; reason: this is the total degree written through the coefficients in $z$
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Proposition 4.13, p.43

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Proposition 4.13: for `L` of characteristic `0` and `f ∈ L[x][z]` irreducible with `d = deg_z f ≥ 1` and
`deg_{x,z} f ≤ D`: (1) `Res_z(f, ∂_z f) ≠ 0` with degree at most `D(D − 1)`; (2) if `f(c, γ) = 0` and the resultant
does not vanish at `c`, then `(∂_z f)(c, γ) ≠ 0`; (3) if the resultant does not vanish at `c`, then the leading
coefficient `ℓ` of `f` satisfies `ℓ(c) ≠ 0`, and so `deg_z f(c, z) = deg_z f`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Proposition 4.13, p.43.

**Formalization Note** `deg_{x,z} f` is the total degree in `x` and `z`, so its bound is written monomial by monomial
through the coefficients of `f` as a polynomial in `z`. -/
theorem proposition_4_13 {L σ : Type*} [Field L] [CharZero L] [Fintype σ] [Nonempty σ]
    (f : Polynomial (MvPolynomial σ L)) (hf : Irreducible f) (hd : 1 ≤ f.natDegree) {D : ℕ}
    (hD : ∀ i ∈ f.support, (f.coeff i).totalDegree + i ≤ D) :
    Polynomial.resultant f (Polynomial.derivative f) ≠ 0 ∧
    (Polynomial.resultant f (Polynomial.derivative f)).totalDegree ≤ D * (D - 1) ∧
    (∀ (c : σ → L) (γ : L), (f.map (eval c)).eval γ = 0 →
      eval c (Polynomial.resultant f (Polynomial.derivative f)) ≠ 0 →
        ((Polynomial.derivative f).map (eval c)).eval γ ≠ 0) ∧
    (∀ c : σ → L, eval c (Polynomial.resultant f (Polynomial.derivative f)) ≠ 0 →
      eval c f.leadingCoeff ≠ 0 ∧ (f.map (eval c)).natDegree = f.natDegree) := by sorry

end BorderD4
