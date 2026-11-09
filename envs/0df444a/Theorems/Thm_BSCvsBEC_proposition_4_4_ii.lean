-- Prove2me | Theorems.Thm_BSCvsBEC_proposition_4_4_ii
-- name    : BSCvsBEC.proposition_4_4_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:33:25.178326+00:00
-- url     : https://prove2.me/theorems/a89cf44b-87b0-44c0-be5f-e1ea1a0b39af
-- title:
--   Proposition 4.4(ii): scalar-to-matrix lifting of $\mathrm{Ent}(T_\eta g)\le c\,\mathrm{Ent}(g)$
-- statement:
--   Fix $0\le\eta\le1$ and $0\le c\le1$. If
--   $$\mathrm{Ent}(T_\eta g)\ \le\ c\,\mathrm{Ent}(g)$$
--   holds for every $g:\mathbb F_2\to\mathbb R_{\ge0}$, then for every finite-dimensional Hilbert space $\mathcal H$ it also holds for every $f:\mathbb F_2\to\mathrm{Pos}(\mathcal H)$:
--   $$\mathrm{Ent}(T_\eta f)\ \le\ c\,\mathrm{Ent}(f).$$
--   Here $T_\eta$ and $\mathrm{Ent}$ are as in §4.2 ($T_\eta$ applied entrywise, $\phi(t)=t\log t$).
--
--   This lifting turns the classical two-point inequality into its matrix-valued version (Corollary 4.5(ii)).
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space ℋ, Pos(ℋ) → ℂ^ι for every finite type ι, positive semidefinite matrices; reason: finite-dimensional Hilbert spaces are ℂ^ι up to unitary isomorphism, and Ent is unitarily invariant
--   - encoding: φ(t) = t log t with log = log₂ by default → natural logarithm; reason: both sides scale by the same factor under a change of base; the paper's proof also uses ln
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Proposition 4.4(ii), eq. (108), p.21; Ent and T_η as in §4.2, p.21

import Mathlib
import Definitions.Def_BSCvsBEC_entF

open scoped ComplexOrder

namespace BSCvsBEC

/-- **Proposition 4.4(ii) (p.21, binary scalar-to-matrix lifting).** Fix `0 ≤ η, c ≤ 1`. If
`Ent(T_η g) ≤ c Ent(g)` (eq. (108)) holds for every `g : F₂ → ℝ_{≥0}`, then it also holds for every
`f : F₂ → Pos(ℋ)`, for every finite-dimensional Hilbert space `ℋ`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Proposition 4.4(ii), p.21, with `Ent` and `T_η` of §4.2, p.21.

**Formalization Note.** `ℋ = ℂ^ι` for an arbitrary finite type `ι`; `Pos(ℋ)` is the positive
semidefinite matrices. `Ent` uses the natural logarithm (the inequality does not depend on the
base). -/
theorem proposition_4_4_ii (η c : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hscalar : ∀ g : Fin 2 → ℝ, (∀ b, 0 ≤ g b) → entR (noiseR η g) ≤ c * entR g) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Fin 2 → Matrix ι ι ℂ),
      (∀ b, (f b).PosSemidef) → entF (noiseOp η f) ≤ c * entF f := by sorry

end BSCvsBEC
