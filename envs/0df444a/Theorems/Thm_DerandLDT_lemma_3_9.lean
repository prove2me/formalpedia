-- Prove2me | Theorems.Thm_DerandLDT_lemma_3_9
-- name    : DerandLDT.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:05:31.862205+00:00
-- url     : https://prove2.me/theorems/11b8101a-4f89-469b-a030-fa33d3ce4a82
-- title:
--   Lemma 3.9 — a non-$p$-th power is a $p$-th power on at most $D$ lines in every direction but one
-- statement:
--   Let $\mathbb F$ be a field of characteristic $p$ and $f(X, Y) \in \mathbb F[X, Y]$ a nonzero polynomial of total degree at most $D$ that is not the $p$-th power of a polynomial in $\mathbb F[X, Y]$. Then there is a direction $\Delta$ such that for every direction $\Delta' \neq \Delta$,
--   $$
--   \#\{ L \text{ a line in direction } \Delta' : f|_L \text{ is the } p\text{-th power of a polynomial} \} \le D .
--   $$
--   In other words, at most one direction is exceptional. The proof of Theorem 1.2 uses it to extract a $p^s$-th root of the polynomial root found on lines in two different directions.
--
--   **Formalization Note** Directions are one-dimensional subspaces of $\mathbb F^2$, and a line is in direction $\Delta'$ when its direction space is $\Delta'$. "$f|_L$ is a $p$-th power" means $f(a + tu) = g(t)^p$ in $\mathbb F[t]$ for a parameterization $(a, u)$ of $L$ (this does not depend on the parameterization). $\mathbb F$ may be infinite, so the count is an extended natural number and the bound includes finiteness.
--
--   Differences from the source:
--   - reading: "there is at most one direction Δ such that for all directions Δ′ ≠ Δ, [the number of p-th-power lines in direction Δ′ is at most D]" → ∃ a direction Δ such that ∀ directions Δ′ ≠ Δ the number is at most D (at most one exceptional direction); reason: the literal quantifier order is false: in characteristic 2, f = XY + X has at most one square restriction per direction, so every direction would qualify; the proof on p.12 proves the reading
--   - encoding: a direction is a nonzero vector up to scalar multiples (u_i, u_j not scalar multiples) → a one-dimensional subspace of F² (finrank 1); r distinct directions = a Finset of r such subspaces; reason: the same object; proportional vectors give one subspace
--   - encoding: "the number of lines … is at most D" → the set of such lines has encard ≤ D; reason: F may be infinite; encard ≤ D also states finiteness
--   - generalization: a field of characteristic p (p-th powers; the proof assumes p prime) → CharP F p for any p, including p = 0; reason: a field's characteristic is prime or 0, so the prime case is an instance; for p = 0 the claim holds since f ≠ 1 and a nonzero f − 1 of total degree ≤ D vanishes on at most D lines
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Lemma 3.9, p.12

import Definitions.Def_LineVsPoint_AffFlat
import Definitions.Def_LineVsPoint_lineRestrict

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

/-- **Lemma 3.9** (`p`-th powers on lines). Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Lemma 3.9, p.12: *Let `F` be any field of
characteristic `p` and `f(X, Y) ∈ F[X, Y]` a nonzero polynomial of total degree at most `D` that
is not the `p`-th power of a polynomial. Then there is at most one direction `Δ` such that for
all directions `Δ′ ≠ Δ` the number of lines `L` in the direction `Δ′` on which the restriction of
`f` is the `p`-th power of a polynomial is at most `D`.*

**Formalization Note.** Read as: there is a direction `Δ` such that for every direction
`Δ′ ≠ Δ`, at most `D` lines in direction `Δ′` carry a `p`-th power, i.e. at most one direction is
exceptional, which is what the proof (p.12) shows. The literal quantifier order is false: in
characteristic `2`, `f = XY + X` has at most one square restriction per direction, so every
direction would qualify. Directions are one-dimensional subspaces of `F²`; a line
(`LineVsPoint.Line F 2`) is in direction `Δ′` when `vectorSpan F L = Δ′`. "`f|_L` is a `p`-th
power" is `f(a + t u) = g(t)^p` in `F[t]` for a parameterization `(a, u)` of `L` (this does not
depend on the parameterization). `F` may be infinite, so "the number … is at most `D`" is
`encard ≤ D`, which includes finiteness. `p` is the characteristic (`CharP F p`), prime or `0`;
for `p = 0` the statement holds as well (`f ≠ 1`, and a nonzero `f − 1` of total degree
`≤ D` vanishes on at most `D` lines). -/
theorem lemma_3_9 (F : Type u) [Field F] (p : ℕ) [CharP F p]
    (f : MvPolynomial (Fin 2) F) (D : ℕ) (hf0 : f ≠ 0) (hfD : f.totalDegree ≤ D)
    (hnp : ¬ ∃ g : MvPolynomial (Fin 2) F, f = g ^ p) :
    ∃ Δ : Submodule F (Fin 2 → F), Module.finrank F Δ = 1 ∧
      ∀ Δ' : Submodule F (Fin 2 → F), Module.finrank F Δ' = 1 → Δ' ≠ Δ →
        {L : LineVsPoint.Line F 2 | vectorSpan F L.carrier = Δ' ∧
          ∃ (a u : Fin 2 → F), u ≠ 0 ∧ L.carrier = Set.range (fun t : F => a + t • u) ∧
            ∃ g : F[X], LineVsPoint.lineRestrict a u f = g ^ p}.encard ≤ D := by sorry

end DerandLDT
