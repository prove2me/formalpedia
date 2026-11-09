-- Prove2me | Theorems.Thm_ForgetAlt_ec_double_paths_eq
-- name    : ForgetAlt.ec_double_paths_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:34.05372+00:00
-- url     : https://prove2.me/theorems/b9839880-9a92-44ba-a020-cf85427a6780
-- title:
--   §3.4: double paths of $(H,E_c)$ are exactly double paths of $(H,E^*)$
-- statement:
--   Let $E_c$ be the set of critical edges of volume $2\ell+5$. A pair of vertex-disjoint paths in $H$ from the endpoints $y,z$ of such an edge to $U$ certifies that the edge is crossable. Hence, for every 4-tuple $(P,Q,y,z)$,
--
--   $$(P,Q,y,z)\text{ is a double path of }(H,E_c)\iff(P,Q,y,z)\text{ is a double path of }(H,E^*).$$
--
--   This is why a double-path algorithm needs no knowledge of $E^*$.
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
--   - encoding: ℓ, with 2ℓ + 1 the length of a shortest augmenting path (|U| ≥ 2 assumed throughout) → hypothesis HasAugPath M; reason: ℓ is undefined when (G, M) has no augmenting path; the hypothesis only excludes that case
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 3.4, unnumbered claim, printed p.23 (PDF p.24)

import Mathlib
import Definitions.Def_ForgetAlt_DoublePathABD

namespace ForgetAlt

open BergeMatching.Core

/-- **Section 3.4, p.23** (PDF p.24), unnumbered claim. Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"… a pair of vertex-disjoint paths in `H` from the endpoints `y` and `z` of a critical edge of
volume `2ℓ + 5` to `U` automatically certifies that the edge is crossable … Hence a double path
of `(H, E_c)`, where `E_c` is the set of all critical edges of volume `2ℓ + 5`, is exactly a
double path of `(H, E*)`."

**Formalization Note.** Paths of `H` between original vertices are paths of `H₀`; `ℓ` requires an
augmenting path to exist. -/
theorem ec_double_paths_eq {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (hA : HasAugPath M) (d : List V × List V × V × V) :
    IsDoublePathABD G M (InEc G M) d ↔ IsDoublePathABD G M (InEstar G M) d := by sorry

end ForgetAlt
