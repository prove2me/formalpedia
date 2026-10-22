-- Prove2me | Theorems.Thm_EastinKnill_Transversal_productUnitaries_compact_subgroup
-- name    : EastinKnill.Transversal.productUnitaries_compact_subgroup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:43.393208+00:00
-- url     : https://prove2.me/theorems/601cc566-9d45-4c4e-81fb-bae39a5c3665
-- title:
--   p. 2 — the unitary product operators $\mathcal T$ form a compact group
-- statement:
--   Let $\mathcal Q$ be a composite system of finitely many subsystems of dimensions $d_j$. The set of unitary product operators
--
--   $$\mathcal T = \Big\{ \bigotimes_j U_j : U_j \in \mathcal U(d_j) \Big\}$$
--
--   is a subgroup of the unitary group of $\mathcal Q$, and it is compact.
--
--   Being the image of the direct product of the compact groups $\mathcal U(d_j)$, $\mathcal T$ is the compact Lie group in which the logical product unitaries live; its compactness is what makes the set of logically distinct transversal actions finite.
--
--   **Formalization Note** "Compact Lie group" is stated as "compact subgroup" of `Matrix.unitaryGroup`; the Lie structure is not formalized.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 2, paragraph defining 𝒯

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem productUnitaries_compact_subgroup {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    [∀ j, DecidableEq (α j)] :
    ∃ T : Subgroup (Matrix.unitaryGroup (∀ j, α j) ℂ),
      (T : Set (Matrix.unitaryGroup (∀ j, α j) ℂ)) = productUnitaries α ∧
      IsCompact (T : Set (Matrix.unitaryGroup (∀ j, α j) ℂ)) := by sorry

end EastinKnill.Transversal
