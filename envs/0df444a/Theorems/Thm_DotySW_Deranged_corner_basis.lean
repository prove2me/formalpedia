-- Prove2me | Theorems.Thm_DotySW_Deranged_corner_basis
-- name    : DotySW.Deranged.corner_basis
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:47.071446+00:00
-- url     : https://prove2.me/theorems/4664bb83-c5ec-41d9-9767-222fbf5113f0
-- title:
--   §4.2 — the basis $\{eDe\}$ of the deranged algebra and $\dim=N(2r)$
-- statement:
--   Let $n\ge2r$, and let $N(k)$ be the number of derangements of $k$ objects. Then:
--
--   1. the $(r,r)$-diagrams with no horizontal edge connecting $i$ to $-i$ number $N(2r)$;
--   2. the elements $eDe$, for these diagrams $D$, are linearly independent;
--   3. they span $e\mathcal B^{(n)}_{r,r}e$;
--   4. $\dim e\mathcal B^{(n)}_{r,r}e=N(2r)$.
--
--   This is the count that gives the deranged algebra its name.
--
--   Differences from the source:
--   - encoding: $N(k)$, the number of derangements of $k$ objects → Mathlib `numDerangements k`; reason: `card_derangements_eq_numDerangements` identifies it with the number of permutations with no fixed point
--   - encoding: $\mathcal B^{(x)}_{r,s}$ over $R[x]$ at $x=n$, over $\mathbb C$ → the published `WalledBrauerAlgebra ℂ r s n`; reason: §3.4 works over ℂ with x = n, and the published algebra has the diagrams as basis and loop parameter n
--   - encoding: $V=\mathbb C^n$ with $n\ge1$ understood → no positivity hypothesis on n; reason: n = 0 is the degenerate case V = 0, where the statement is still true, and no instance with n ≥ 1 changes
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.2, unnumbered, p. 11

import Mathlib
import Definitions.Def_DotySW_Deranged_corner
import Definitions.Def_DotySW_Deranged_NoFixedArc

namespace DotySW.Deranged

open WalledBrauer.Blocks

/-- **The basis `{eDe}` of the deranged algebra and its dimension `N(2r)`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.2, unnumbered, p. 11.

For `n ≥ 2r`, the `(r, r)`-diagrams with no horizontal edge connecting `i` to `-i` number `N(2r)`,
the elements `eDe` for these diagrams are linearly independent and span `e B^{(n)}_{r,r} e`, and
that algebra has dimension `N(2r)`.

**Formalization Note** `N(k)` is Mathlib's `numDerangements k`, which
`card_derangements_eq_numDerangements` identifies with the number of permutations with no fixed
point. -/
theorem corner_basis (n r : ℕ) (h : 2 * r ≤ n) :
    Nat.card {D : WalledDiagram r r // NoFixedArc D} = numDerangements (2 * r) ∧
    LinearIndependent ℂ
      (fun D : {D : WalledDiagram r r // NoFixedArc D} =>
        eIdem n r * (diag D.1 : WB n r r) * eIdem n r) ∧
    Submodule.span ℂ (Set.range
      (fun D : {D : WalledDiagram r r // NoFixedArc D} =>
        eIdem n r * (diag D.1 : WB n r r) * eIdem n r)) = corner n r ∧
    Module.finrank ℂ (corner n r) = numDerangements (2 * r) := by sorry

end DotySW.Deranged
