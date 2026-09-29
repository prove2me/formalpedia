-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_riemannRochSpace_nsmul_poleDivisor_normalForm
-- name    : AlgebraicCurve.exists_riemannRochSpace_nsmul_poleDivisor_normalForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/d6ab8983-19af-506d-833b-52d19c4037b9
-- title:
--   Split Riemann–Roch normal form of weights (0,1^g,2^g)
-- statement:
--   Let $K$ be an algebraically closed field, $F$ a field which is a $K$-algebra, and suppose some element of $F$ is transcendental over $K$ and makes $F$ finite-dimensional over the intermediate field it generates. Write $g=\mathrm{genusFF}\,K\,F$, the $K$-dimension of `H1` of the zero divisor. Then there exist $x\in F$, a divisor $D$ (a finitely supported integer-valued function on the places of $F/K$, a place being a proper valuation subring of $F$ containing the image of $K$ whose ring is a principal ideal ring), elements $e_i\in F$, natural numbers $d_i$, polynomials $q_{ijk}\in K[X]$ and scalars $\tau_{ji}\in K$, all indexed by $\mathrm{Fin}(2g+1)$, such that: $x$ is transcendental over $K$, $F$ is finite over $K(x)$ of degree $2g+1$; $D(v)=\max(0,-\mathrm{ord}_v x)$ for every place $v$, where $\mathrm{ord}_v$ is minus the logarithm of the adic valuation attached to $v$; $e_0=1$, $d_0=0$, $d_i\in\{1,2\}$ for $i\neq 0$, and $\sum_i d_i=3g$; for every $k\in\mathbb{N}$, an $f\in F$ satisfies $v(f)\le \exp(kD(v))$ at all $v$ exactly when $f=\sum_i c_i(x)e_i$ with $\deg c_i<k+1-d_i$ (truncated subtraction); the $e_i$ are linearly independent over $K[x]$; every $z\in F$ satisfies $r(x)z\in L(kD)$ for some nonzero $r\in K[X]$ and some $k$; $e_ie_j=\sum_k q_{ijk}(x)e_k$ with $\deg q_{ijk}\le d_i+d_j-d_k$ whenever $i,j\neq 0$; and $\det(\tau)$ is a unit, $\tau_{j0}=1$, and $\tau_{ji}\tau_{ji'}=\sum_k [X^{d_i+d_{i'}-d_k}]q_{ii'k}\cdot\tau_{jk}$ for $i,i'\neq 0$.
--
--   This is the normalisation step for one-variable function fields over an algebraically closed field: it produces a coordinate $x$ whose pole divisor is reduced of degree $2g+1$, a free $K[x]$-basis $e_0,\dots,e_{2g}$ of the functions regular away from the poles of $x$ with weights $(0,1^g,2^g)$ governing the Riemann–Roch filtration $L(kD)$, structure constants $q_{ijk}$ of bounded degree, and a matrix $\tau$ recording that the leading forms at the poles split into $2g+1$ rational points. It feeds the construction of good constant reductions of curves, being cited by [`AlgebraicCurve.exists_charZero_constantReduction_isGood`](thm.html#AlgebraicCurve.exists_charZero_constantReduction_isGood).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_riemannRochSpace_nsmul_poleDivisor_normalForm.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial
open AlgebraicCurve

universe u v

theorem AlgebraicCurve.exists_riemannRochSpace_nsmul_poleDivisor_normalForm
    (K : Type u) (F : Type v) [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (hF : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ (x : F) (D : Divisor K F) (e : Fin (2 * genusFF K F + 1) → F)
      (d : Fin (2 * genusFF K F + 1) → ℕ)
      (q : Fin (2 * genusFF K F + 1) → Fin (2 * genusFF K F + 1) → Fin (2 * genusFF K F + 1) → K[X])
      (τ : Fin (2 * genusFF K F + 1) → Fin (2 * genusFF K F + 1) → K),
      Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F ∧
      Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F = 2 * genusFF K F + 1 ∧
      (∀ v : Place K F, D v = max 0 (-v.ord x)) ∧
      e 0 = 1 ∧ d 0 = 0 ∧ (∀ i, i ≠ 0 → d i = 1 ∨ d i = 2) ∧ (∑ i, d i = 3 * genusFF K F) ∧
      (∀ (k : ℕ) (f : F), f ∈ riemannRochSpace (k • D) ↔
        ∃ c : Fin (2 * genusFF K F + 1) → K[X],
          (∀ i, c i ∈ Polynomial.degreeLT K (k + 1 - d i)) ∧
          f = ∑ i, Polynomial.aeval x (c i) * e i) ∧
      (∀ c : Fin (2 * genusFF K F + 1) → K[X], ∑ i, Polynomial.aeval x (c i) * e i = 0 → c = 0) ∧
      (∀ z : F, ∃ r : K[X], r ≠ 0 ∧ ∃ k : ℕ, Polynomial.aeval x r * z ∈ riemannRochSpace (k • D)) ∧
      (∀ i j, e i * e j = ∑ k, Polynomial.aeval x (q i j k) * e k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (q i j k).natDegree ≤ d i + d j - d k) ∧
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      (∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, (q i i' k).coeff (d i + d i' - d k) * τ j k) := by sorry
