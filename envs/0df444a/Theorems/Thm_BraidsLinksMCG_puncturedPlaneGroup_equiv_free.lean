-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_equiv_free
-- name    : BraidsLinksMCG.puncturedPlaneGroup_equiv_free
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-21T18:12:42.648836+00:00
-- url     : https://prove2.me/theorems/913cdc00-34fd-4d0c-b32c-4e5d52ef01f7
-- title:
--   $\pi_1$ of the $n$-punctured plane is free of rank $n$
-- statement:
--   The fundamental group of the plane punctured at $n$ points is free of rank $n$:
--
--   $$\pi_1igl(E^{2} - Q_nigr) \;\cong\; F_n.$$
--
--   Here $Q_n = \{1, 2, \ldots, n\} \subset \mathbb{C}$ and the base point is $n+1$, as fixed by the platform's `PuncturedPlane` and `basePunctured`.
--
--   This is the first of the two statements bundled in `BraidsLinksMCG.cor_1_8_1_pure_braid_semidirect`, separated out because it is independent of the other one and is needed elsewhere on its own. It is the identification that makes Artin's representation possible at all: a braid acts on the punctured plane up to isotopy, hence on its fundamental group, and it is only through this isomorphism that the action becomes an automorphism of a free group on which Artin's formulas can be written.
--
--   The classical proof is a deformation retraction followed by van Kampen: the punctured plane retracts onto a wedge of $n$ circles, one around each puncture, and the fundamental group of a wedge of circles is free on the loops. Concretely the free generators are the loops $x_j$ that run from the base point to near the $j$-th puncture, encircle it once counterclockwise, and return along the same path.
--
--   The statement is deliberately phrased as `Nonempty`, asserting only that some isomorphism exists. Applications that need to know where the standard loops go will require a generator-matched strengthening; that is not claimed here.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, Theorem 1.4 and Corollary 1.8.1; Fadell and Neuwirth, Configuration spaces.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem puncturedPlaneGroup_equiv_free (n : ℕ) :
    Nonempty (PuncturedPlaneGroup n ≃* FreeGroup (Fin n)) := by sorry

end BraidsLinksMCG
