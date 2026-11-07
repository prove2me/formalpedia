-- Prove2me | Theorems.Thm_BorderD4_lemma_2_10
-- name    : BorderD4.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:07.943194+00:00
-- url     : https://prove2.me/theorems/95db19df-8b1f-48a6-be8c-1686d10983b9
-- title:
--   Lemma 2.10: $\mathrm{DEG}\,p\le\delta^{\mathrm{ht}\,p}\le\delta^r$
-- statement:
--   Let $L$ be a field and let $q_1,\dots,q_r\in L[x]$ be nonconstant polynomials of degree at most $\delta$. If $p$ is a minimal prime of $\langle q_1,\dots,q_r\rangle$, then
--   $$\mathrm{DEG}\,p\le\delta^{\mathrm{ht}\,p}\le\delta^{r}.$$
--   This is a consequence of the Bézout inequalities for polynomial ideals, used to bound the degree of the prime chosen in Lemma 6.9.
--
--   Differences from the source:
--   - encoding: the variables $x_1,\dots,x_N$ → an arbitrary finite nonempty index type; reason: any such type is $[N]$ up to renaming
--   - encoding: $\mathrm{DEG}$ as a number → the predicate `HasDEG I D`, with the conclusion $\exists D$; reason: no junk value can satisfy a bound; the Hilbert polynomial is asserted to exist
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 2.10, p.32

import Mathlib
import Definitions.Def_BorderD4_HasDEG
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Lemma 2.10: for nonconstant `q_1, …, q_r ∈ L[x]` of degree at most `δ` and a minimal prime `p` of
`⟨q_1, …, q_r⟩`, `DEG p ≤ δ^{ht p} ≤ δ^r`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 2.10, p.32. -/
theorem lemma_2_10 {L σ : Type*} [Field L] [Fintype σ] [Nonempty σ] {δ r : ℕ}
    (q : Fin r → MvPolynomial σ L) (hq : ∀ i, (q i).totalDegree ≠ 0)
    (hδ : ∀ i, (q i).totalDegree ≤ δ) (p : Ideal (MvPolynomial σ L))
    (hp : p ∈ (Ideal.span (Set.range q)).minimalPrimes) :
    ∃ D h : ℕ, HasDEG p D ∧ p.height = h ∧ D ≤ δ ^ h ∧ δ ^ h ≤ δ ^ r := by sorry

end BorderD4
