-- Prove2me | Theorems.Thm_DerandLDT_corollary_3_12
-- name    : DerandLDT.corollary_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:13.118594+00:00
-- url     : https://prove2.me/theorems/43c614bd-2b6a-4099-8fb0-42cfbe40e1eb
-- title:
--   Corollary 3.12 — $f$ squarefree iff $\mathrm{Disc}(f) \ne 0$ over finite or characteristic-zero fields
-- statement:
--   Let $\mathbb F$ be a finite field or a field of characteristic zero, and let $f \in \mathbb F[X]$ have degree at least two. Then
--   $$
--   f \text{ is squarefree} \iff \mathrm{Disc}(f) \neq 0,
--   $$
--   where $\mathrm{Disc}(f) = \mathrm{Res}(f, \partial f)$ is the resultant of $f$ and its first-order Hasse derivative (Definition 3.10).
--
--   The paper uses this at a good point $a$ to conclude that $\hat Q(a, Z)$ and $\partial_Z \hat Q(a, Z)$ have no common zero.
--
--   **Formalization Note** $\mathrm{Disc}$ is `DerandLDT.disc`.
--
--   Differences from the source:
--   - encoding: Disc(f) = Res(f, f⁽¹⁾) with the Sylvester matrix of Definition 3.10 (degrees ≥ 1) → Mathlib's resultant with the default sizes deg f, deg ∂f; reason: the same matrix when deg ∂f ≥ 1; Mathlib's convention extends it when ∂f is constant or zero
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Corollary 3.12, p.13

import Definitions.Def_DerandLDT_disc

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

/-- **Corollary 3.12** (squarefree iff nonzero discriminant). Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Corollary 3.12, p.13:
*Let `F` be a finite field or a field of characteristic zero and `f ∈ F[X]` a polynomial of
degree at least two. Then `f` is squarefree iff `Disc(f)` is nonzero.*

**Formalization Note.** `Disc(f) = Res(f, f⁽¹⁾)` is `DerandLDT.disc` (Definition 3.10), the
resultant with Mathlib's default Sylvester sizes, which are the paper's when `deg f⁽¹⁾ ≥ 1`. -/
theorem corollary_3_12 (F : Type u) [Field F] (hF : Finite F ∨ CharZero F) (f : F[X])
    (hf : 2 ≤ f.natDegree) : Squarefree f ↔ disc f ≠ 0 := by sorry

end DerandLDT
