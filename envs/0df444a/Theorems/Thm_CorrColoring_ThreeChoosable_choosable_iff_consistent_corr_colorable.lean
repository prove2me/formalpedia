-- Prove2me | Theorems.Thm_CorrColoring_ThreeChoosable_choosable_iff_consistent_corr_colorable
-- name    : CorrColoring.ThreeChoosable.choosable_iff_consistent_corr_colorable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:03:45.334405+00:00
-- url     : https://prove2.me/theorems/6c5a9611-86e9-4758-aed8-57523d1187e0
-- title:
--   Lemma 5 — $G$ is $k$-choosable iff $G$ is $C$-colorable for every consistent $k$-correspondence assignment $C$
-- statement:
--   Let $G$ be a finite simple graph and $k \ge 0$. Then
--
--   $$G \text{ is } k\text{-choosable} \iff G \text{ is } C\text{-colorable for every consistent } k\text{-correspondence assignment } C .$$
--
--   Here consistency means consistency on every closed walk of $G$. List colouring is therefore exactly correspondence colouring restricted to consistent assignments; this is how Theorem 1 follows from the correspondence-colouring Theorem 6.
--
--   **Formalization Note** $k$-choosability quantifies over lists of exactly $k$ colours from an arbitrary colour type; $[k]$ is `Fin k`.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 6, Lemma 5

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_IsChoosable
import Definitions.Def_CorrColoring_ThreeChoosable_KCorrAssignment
import Definitions.Def_CorrColoring_ThreeChoosable_ConsistentOn

namespace CorrColoring.ThreeChoosable

/-- Lemma 5 (Dvořák–Postle, p. 6). -/
theorem choosable_iff_consistent_corr_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) :
    IsChoosable G k ↔
      ∀ C : KCorrAssignment G k, Consistent C → ∃ φ : V → Fin k, IsCColoring C φ := by sorry

end CorrColoring.ThreeChoosable
