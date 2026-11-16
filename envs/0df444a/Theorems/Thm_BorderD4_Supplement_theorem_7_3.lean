-- Prove2me | Theorems.Thm_BorderD4_Supplement_theorem_7_3
-- name    : BorderD4.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:03:42.579388+00:00
-- url     : https://prove2.me/theorems/ecaa3638-cddf-40b5-b58c-82b191e29127
-- title:
--   Theorem 7.3 — at most $\Delta$ components at infinity, each of dimension $d-1$
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $0$. Let $W_0\subseteq\mathbb A^N$ be an irreducible affine variety of degree $\Delta$ and dimension $d\ge1$, let $W\subseteq\mathbb P^N$ be its projective closure, $H_\infty$ the hyperplane at infinity, and $\nu:\widetilde W\to W$ the normalization. Put
--   $$D_\infty:=\nu^{-1}(W\cap H_\infty).$$
--   Then $D_\infty$ has at most $\Delta$ irreducible components, and each of them has dimension $d-1$.
--
--   The components of $D_\infty$ are the divisors at infinity along which the units of $F[W_0]$ have their zeros and poles; the bound feeds the rank bound of Theorem 7.4.
--
--   **Formalization Note** $W_0=V(p)$ for a prime $p\subseteq F[x_1,\dots,x_N]$, $\deg W_0$ is the published `BorderD4.HasDEG`, and $\dim W_0$ is the Krull dimension of $F[x]/p$. The components of $D_\infty$ are encoded as the minimal primes $P$ of $x_0\widetilde S$, where $\widetilde S$ is the integral closure of $F[x_0,\dots,x_N]/p^h$ in its fraction field; a component has dimension $\dim\widetilde S/P-1$.
--
--   Differences from the source:
--   - encoding: W_0 ⊆ A^N irreducible of degree Δ and dimension d → a prime ideal p of F[x_1..x_N] with HasDEG p Δ and ringKrullDim (F[x]/p) = d; reason: over an algebraically closed field W_0 ↦ I(W_0) is a bijection onto prime ideals; deg W_0 = DEG I(W_0) (p.31); dim = Krull dimension
--   - encoding: the irreducible components of D_∞ = ν^{-1}(W ∩ H_∞) and their dimensions → the minimal primes P of x_0·S̃, S̃ the integral closure of F[x_0..x_N]/p^h in its fraction field (finite set of cardinality ≤ Δ), with ringKrullDim (S̃/P) = d; reason: W̃ = Proj S̃ is the normalization of W = Proj S; ν^{-1}(V_+(x_0)) = V_+(x_0 S̃), whose components are V_+(P) for these P (homogeneous, of height one, relevant since d ≥ 1), and dim V_+(P) = dim S̃/P − 1
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 7.3, p.80; standing assumptions p.3 and §7, p.77; §7.1, pp.77–78; §2.2, p.31

import Mathlib
import Definitions.Def_BorderD4_HasDEG
import Definitions.Def_BorderD4_Supplement_componentsAtInfinity
set_option autoImplicit false

open MvPolynomial

namespace BorderD4.Supplement

/-- Theorem 7.3: irreducible components at infinity of the normalized projective closure.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 7.3, p.80; standing assumptions p.3 (characteristic `0`) and §7, p.77 (`F` algebraically closed); projective closure and normalization, §7.1, pp.77–78; degree, §2.2, p.31.

Let `W_0 ⊆ A^N` be an irreducible affine variety of degree `∆` and dimension `d ≥ 1`, `W ⊆ P^N` its projective
closure, `H_∞` the hyperplane at infinity, `ν : W̃ → W` the normalization and `D_∞ := ν^{-1}(W ∩ H_∞)`. Then `D_∞`
has at most `∆` irreducible components, each of dimension `d − 1`.

**Formalization Note** `W_0 = V(p)` for its prime ideal `p ⊆ F[x_1, …, x_N]`; `deg W_0 = ∆` is the published
`BorderD4.HasDEG p ∆`; `dim W_0 = d` is the Krull dimension of `F[x]/p`. The components of `D_∞` are encoded by
`componentsAtInfinity p`, the minimal primes `P` of `x_0 S̃` in the homogeneous coordinate ring `S̃` of `W̃` (the
integral closure of `F[x_0, …, x_N]/p^h` in its fraction field); the component `V_+(P)` has dimension
`dim S̃/P − 1`, so "dimension `d − 1`" is `dim S̃/P = d`. -/
theorem theorem_7_3 {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] {N : ℕ}
    (p : Ideal (MvPolynomial (Fin N) F)) (hp : p.IsPrime) (Δ d : ℕ) (hΔ : BorderD4.HasDEG p Δ)
    (hdim : ringKrullDim (MvPolynomial (Fin N) F ⧸ p) = d) (hd : 1 ≤ d) :
    (componentsAtInfinity p).Finite ∧ (componentsAtInfinity p).ncard ≤ Δ ∧
      ∀ P ∈ componentsAtInfinity p, ringKrullDim (normalizedCone p ⧸ P) = d := by sorry

end BorderD4.Supplement
