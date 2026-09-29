-- Prove2me | Theorems.Thm_Erdos180_subdivisionLine_bases_disjoint
-- name    : Erdos180.subdivisionLine_bases_disjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:08:27.401998+00:00
-- url     : https://prove2.me/theorems/b25a957e-591a-433a-8e90-2f761e66c766
-- title:
--   Distinct bases land on disjoint lines
-- statement:
--   If a copy of $S_k$ in $I_q$ sends the bases to lines $L(1), L(2), L(3)$, then distinct
--   bases give lines meeting only in the zero subspace.
--
--   Two lines of the quadrangle meeting in a point would be *related*, and Lemma 3.1(2) states that
--   the bases of a copy of $S_k$ form an $R_S$-independent triple. Disjointness is the linear-algebra
--   form of that independence, and it is the hypothesis under which the normalisation of a line
--   pair — and hence the characteristic-two computation of Proposition 4.2 — applies.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2581-L2638

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionLine_bases_disjoint
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (L : Fin 3 → SymplecticLine K)
    (C : Fin k → SymplecticLine K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inr (L base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    Disjoint (L i).1 (L j).1 := by sorry
