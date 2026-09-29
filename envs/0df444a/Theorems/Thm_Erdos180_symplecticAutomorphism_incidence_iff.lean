-- Prove2me | Theorems.Thm_Erdos180_symplecticAutomorphism_incidence_iff
-- name    : Erdos180.symplecticAutomorphism_incidence_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:15:45.596401+00:00
-- url     : https://prove2.me/theorems/4f0bc195-0fdf-4bfc-be02-5a92811fedbf
-- title:
--   Symplectic automorphisms preserve incidence
-- statement:
--   For a symplectic automorphism $e$, a point $p$ and a line $L$,
--
--   $$e(p) \le e(L) \iff p \le L .$$
--
--   The action of $\mathrm{Sp}_4$ on $W(q)$ is by automorphisms of the incidence structure. This is
--   what makes the normalisation of §4 legitimate: an arbitrary disjoint line pair may be moved to a
--   standard one without changing any incidence-theoretic hypothesis.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6779-L6789

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticAutomorphism_incidence_iff
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticAutomorphismPoint K e p).1 ≤
        (symplecticAutomorphismLine K e L).1 ↔
      p.1 ≤ L.1 := by sorry
