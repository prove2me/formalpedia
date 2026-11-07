-- Prove2me | Theorems.Thm_BorderD4_lemma_6_9
-- name    : BorderD4.lemma_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:34.658715+00:00
-- url     : https://prove2.me/theorems/0fb9f960-890c-4584-8977-2c4fdb6a1323
-- title:
--   Lemma 6.9: choosing the gates for cancellation
-- statement:
--   Let $T_1,\dots,T_k\in F[[\varepsilon]][x]$ with $T_i=\prod_j q_{i,j}$, where each $q_{i,j}$ is nonzero and has degree at most $\delta$ in $x$. There exist a set $K\subseteq[k]$ of surviving gates and a prime ideal $p\subseteq F((\varepsilon))[x]$ such that $I:=p\cap F[[\varepsilon]][x]$ satisfies:
--
--   1. $I\subseteq\langle\varepsilon,x_1,\dots,x_N\rangle$;
--   2. $\mathrm{ht}\,p\le k-|K|$ and $\mathrm{DEG}\,p\le\delta^{k-|K|}$;
--   3. $T_i\in I$ for every $i\notin K$;
--   4. for every $i\in K$ and every $j$, there are $t\ge 0$ and $h,w\in F[[\varepsilon]][x]$ with $h(0,0)\ne 0$ and $q_{i,j}w\equiv\varepsilon^t h\pmod I$.
--
--   Here $F$ is algebraically closed of characteristic zero, §6's standing assumption. Gates outside $K$ vanish on $I$, and the factors of the others are invertible near the origin up to powers of $\varepsilon$.
--
--   Differences from the source:
--   - generalization: §6 fixes $N=(k+1)n$ (p.49) → an arbitrary finite nonempty index type; reason: the proof uses $N$ only as the number of variables; $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$ is the source
--   - encoding: $\mathrm{DEG}$ as a number → the predicate `HasDEG I D`, with the conclusion $\exists D$; reason: no junk value can satisfy a bound; the Hilbert polynomial is asserted to exist
--   - encoding: $T_i=\prod_j q_{i,j}$ → a list of factors for each $i$; reason: a finite product is a list
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.9, p.54

import Mathlib
import Definitions.Def_BorderD4_HasDEG
import Definitions.Def_BorderD4_toK
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Lemma 6.9, choosing the gates for cancellation: for `T_i = ∏_j q_{i,j} ∈ F[[ε]][x]` with nonzero factors of
degree at most `δ` in `x`, there are a set `K ⊆ [k]` of surviving gates and a prime `p ⊆ F((ε))[x]` such that
`I := p ∩ F[[ε]][x]` satisfies Items 1–4.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.9, p.54.

**Formalization Note** `h(0, 0)` sets both `ε` and `x` to `0`. The congruence `q_{i,j} w ≡ ε^t h (mod I)` is the
membership of the difference in `I`. -/
theorem lemma_6_9 {F σ : Type*} [Field F] [IsAlgClosed F] [CharZero F] [Fintype σ] [Nonempty σ]
    {k δ : ℕ} (_hk : 1 ≤ k) (_hδ : 1 ≤ δ) (q : Fin k → List (MvPolynomial σ F⟦X⟧))
    (hq0 : ∀ i, ∀ x ∈ q i, x ≠ 0) (hqdeg : ∀ i, ∀ x ∈ q i, x.totalDegree ≤ δ) :
    ∃ (K : Finset (Fin k)) (p : Ideal (MvPolynomial σ (LaurentSeries F))), p.IsPrime ∧
      p.comap toK ≤ epsXIdeal F σ ∧
      p.height ≤ ((k - K.card : ℕ) : ℕ∞) ∧ (∃ D, HasDEG p D ∧ D ≤ δ ^ (k - K.card)) ∧
      (∀ i, i ∉ K → (q i).prod ∈ p.comap toK) ∧
      (∀ i ∈ K, ∀ x ∈ q i, ∃ (t : ℕ) (h w : MvPolynomial σ F⟦X⟧),
        PowerSeries.constantCoeff (constantCoeff h) ≠ 0 ∧
          x * w - MvPolynomial.C PowerSeries.X ^ t * h ∈ p.comap toK) := by sorry

end BorderD4
