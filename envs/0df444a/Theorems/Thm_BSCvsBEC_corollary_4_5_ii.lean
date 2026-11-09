-- Prove2me | Theorems.Thm_BSCvsBEC_corollary_4_5_ii
-- name    : BSCvsBEC.corollary_4_5_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:33:29.347023+00:00
-- url     : https://prove2.me/theorems/fa1c0bbc-656b-4207-a3ef-a3bd496e4345
-- title:
--   Corollary 4.5(ii): $\mathrm{Ent}(T_\eta f)\le\eta^2\,\mathrm{Ent}(f)$ for $f:\mathbb F_2\to\mathrm{Pos}(\mathcal H)$
-- statement:
--   Let $\mathcal H$ be a finite-dimensional Hilbert space, $f:\mathbb F_2\to\mathrm{Pos}(\mathcal H)$ a function into positive semidefinite operators, and $0\le\eta\le1$. Then
--   $$\mathrm{Ent}(T_\eta f)\ \le\ \eta^2\,\mathrm{Ent}(f),$$
--   where $T_\eta f(b)=\tfrac{1+\eta}2f(b)+\tfrac{1-\eta}2f(b+1)$ and $\mathrm{Ent}(f)=\mathbb E_b\operatorname{Tr}\phi(f(b))-\operatorname{Tr}\phi(\mathbb Ef)$, $\phi(t)=t\log t$.
--
--   This is the matrix-valued one-bit Shannon Samorodnitsky inequality; applied to $f(0)=B$, $f(1)=JBJ$ with $\eta=\cos\theta$ it yields Theorem 4.2.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space ℋ, Pos(ℋ) → ℂ^ι for a finite type ι, positive semidefinite matrices; reason: finite-dimensional Hilbert spaces are ℂ^ι up to unitary isomorphism, and Ent is unitarily invariant
--   - encoding: φ(t) = t log t with log = log₂ by default → natural logarithm; reason: both sides scale by the same factor under a change of base; the paper's proof also uses ln
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Corollary 4.5(ii), eq. (112), p.22; Ent and T_η as in §4.2, p.21

import Mathlib
import Definitions.Def_BSCvsBEC_entF

open scoped ComplexOrder

namespace BSCvsBEC

/-- **Corollary 4.5(ii) (p.22).** Let `f : F₂ → Pos(ℋ)` and `0 ≤ η ≤ 1`. Then
`Ent(T_η f) ≤ η² Ent(f)` (eq. (112)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Corollary 4.5(ii), p.22, with `Ent` and `T_η` of §4.2, p.21.

**Formalization Note.** `ℋ = ℂ^ι` for an arbitrary finite type `ι`; `Pos(ℋ)` is the positive
semidefinite matrices; `Ent` uses the natural logarithm. -/
theorem corollary_4_5_ii (ι : Type) [Fintype ι] [DecidableEq ι] (f : Fin 2 → Matrix ι ι ℂ)
    (hf : ∀ b, (f b).PosSemidef) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    entF (noiseOp η f) ≤ η ^ 2 * entF f := by sorry

end BSCvsBEC
