-- Prove2me | Theorems.Thm_FanoUnique_lines_meet
-- name    : FanoUnique.lines_meet
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T19:24:55.024988+00:00
-- url     : https://prove2.me/theorems/16033309-8b7e-4a15-8b8c-0be4a915936d
-- title:
--   Corollary B: any two distinct lines of an STS(7) meet in exactly one point
-- statement:
--   Let $S$ be a Steiner triple system on $\{0, \dots, 6\}$. Any two distinct lines $\ell \neq \ell'$ of $S$ share exactly one point:
--
--   $$
--   |\ell \cap \ell'| = 1 .
--   $$
--
--   At most one, because a shared pair would lie on two lines; at least one, because the $3$ points of a line each lie on $2$ further lines, giving $6$ lines that meet it — all of the others.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3, proof of Theorem 3.3 ("Uniqueness of STS(7) is classical"); obtained as a corollary of that uniqueness: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; public references: Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Steiner system": https://en.wikipedia.org/wiki/Steiner_system

import Mathlib
import Definitions.Def_FanoUnique_isFano

namespace FanoUnique

open RolesForceSeven

theorem lines_meet (S : STS 7) :
    ∀ l ∈ S.lines, ∀ l' ∈ S.lines, l ≠ l' → (l ∩ l').card = 1 := by
  sorry

end FanoUnique
