-- Prove2me | Theorems.Thm_CubicSurface27_transverse_implies_twenty_seven
-- name    : CubicSurface27.transverse_implies_twenty_seven
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T01:53:36.872387+00:00
-- url     : https://prove2.me/theorems/3815f646-bd10-4f4f-aac9-bb1b58b5bc4d
-- title:
--   Transverse zeroes of $s_F$ imply exactly $27$ lines
-- statement:
--   If $s_F$ has transverse zeroes, then $X$ contains exactly $27$ lines.
--
--   Let $F$ be a homogeneous cubic polynomial in four variables over $\mathbb{C}$, and assume the associated section $s_F$ of $\mathrm{Sym}^3 S^*$ on $\mathrm{Gr}(2,4)$ has transverse zeroes. Then the set of lines on $V(F)$ is finite of cardinality $27$:
--   $$
--   \#\{\text{lines on }V(F)\}=27.
--   $$
--
--   This is the "therefore" of the source's final theorem. Transversality, not smoothness, is the hypothesis that promotes the Chern-class computation $c_4(\mathrm{Sym}^3 S^*)=27\sigma_{22}$ from an expected count to an actual count of distinct lines. The source records that finiteness alone yields only the weaker bound of at most $27$ lines, counted with multiplicity; a non-transverse zero may contribute multiplicity greater than one.
--
--   **Formalization Note.** Transverse zeroes are `HasTransverseZeroes`. The cardinality is `Set.ncard (linesOf F)`, hence the equality includes finiteness. Smoothness is not a hypothesis: the source uses it only to reach transversality.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part II, final Theorem: "If X is smooth, then s_F has transverse zeroes. Therefore X contains exactly 27 lines." Second sentence ("Therefore $X$ contains exactly $27$ lines"), using the transverse-zeroes hypothesis isolated in "The lie."

import Definitions.Def_cubic_surface_27_layer
import Definitions.Def_cubic_surface_transverse

namespace CubicSurface27

theorem transverse_implies_twenty_seven (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (ht : HasTransverseZeroes F) :
    (linesOf F).ncard = 27 := by sorry

end CubicSurface27
