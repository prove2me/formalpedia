-- Prove2me | Theorems.Thm_BorderD4_lemma_6_10
-- name    : BorderD4.lemma_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:01.994199+00:00
-- url     : https://prove2.me/theorems/20aa0054-abd1-4a6c-8a28-7c053962913f
-- title:
--   Lemma 6.10: a low-weight point on a variety
-- statement:
--   Let $V\subseteq\mathbb A^N$ be an irreducible affine variety of codimension $C$ that contains $0$, over an algebraically closed $F$ of characteristic $0$. Let $g\in F[x]$ not vanish identically on $V$, and let $h_1,\dots,h_t\in F[x]$ satisfy $h_j(0)\ne 0$. There exists $b\in V$ with
--   $$g(b)h_1(b)\cdots h_t(b)\ne 0,\qquad |\mathrm{supp}(b)|\le(C+1)\cdot\deg V\cdot\deg g.$$
--   The bound depends neither on $t$ nor on the degrees of the $h_j$, which is what lets the point avoid the zeros of every factor of the surviving gates at no cost.
--
--   Differences from the source:
--   - generalization: §6 fixes $N=(k+1)n$ (p.49) → an arbitrary finite nonempty index type; reason: the proof uses $N$ only as the number of variables; $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$ is the source
--   - encoding: irreducible varieties over algebraically closed $F$ → their prime ideals (minimal primes for components); reason: the Nullstellensatz correspondence stated on p.30
--   - encoding: $\mathrm{DEG}$ as a number → the predicate `HasDEG I D`, with the conclusion $\exists D$; reason: no junk value can satisfy a bound; the Hilbert polynomial is asserted to exist
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.10, p.56

import Mathlib
import Definitions.Def_BorderD4_HasDEG
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Lemma 6.10, a low-weight point: for an irreducible variety `V` of codimension `C` containing `0`, a polynomial `g`
not vanishing identically on `V`, and `h_1, …, h_t` with `h_j(0) ≠ 0`, there is `b ∈ V` with
`g(b) h_1(b) ⋯ h_t(b) ≠ 0` and `|supp(b)| ≤ (C + 1) · deg V · deg g`. The bound depends neither on `t` nor on the
degrees of the `h_j`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.10, p.56.

**Formalization Note** `F` is algebraically closed, so `V` is `V(𝔮)` for a prime `𝔮` of `F[x]`, with `C = ht 𝔮`,
`deg V = DEG 𝔮`, `0 ∈ V` meaning every element of `𝔮` vanishes at `0`, and `g` not vanishing identically on `V` meaning
`g ∉ 𝔮` (p.30). -/
theorem lemma_6_10 {F σ : Type*} [Field F] [IsAlgClosed F] [CharZero F] [Fintype σ] [Nonempty σ]
    (𝔮 : Ideal (MvPolynomial σ F)) [𝔮.IsPrime] (C : ℕ) (hC : 𝔮.height = C)
    (h0 : ∀ g' ∈ 𝔮, eval (0 : σ → F) g' = 0) (g : MvPolynomial σ F) (hg : g ∉ 𝔮) {t : ℕ}
    (h : Fin t → MvPolynomial σ F) (hh : ∀ j, eval (0 : σ → F) (h j) ≠ 0) :
    ∃ (D : ℕ) (b : σ → F), HasDEG 𝔮 D ∧ (∀ g' ∈ 𝔮, eval b g' = 0) ∧
      eval b g * ∏ j, eval b (h j) ≠ 0 ∧
      (Function.support b).ncard ≤ (C + 1) * D * g.totalDegree := by sorry

end BorderD4
