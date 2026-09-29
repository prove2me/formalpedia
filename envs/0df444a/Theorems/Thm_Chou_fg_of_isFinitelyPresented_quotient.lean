-- Prove2me | Theorems.Thm_Chou_fg_of_isFinitelyPresented_quotient
-- name    : Chou.fg_of_isFinitelyPresented_quotient
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-09-19T11:59:34.157366+00:00
-- url     : https://prove2.me/theorems/d8196f52-dddb-4a8f-9da4-8a0489b78722
-- title:
--   Superseded, and open: in an exponentially bounded group a normal subgroup with finitely presented quotient is finitely generated — use Chou.fg_of_isVirtuallyPolycyclic_quotient
-- statement:
--   If $G$ is finitely generated and exponentially bounded, and $N$ is a normal subgroup with
--   $G/N$ finitely presented, then $N$ is finitely generated.
--
--   **Superseded.** This statement asserts finite generation from a finitely presented quotient. Milnor's Lemma 2 (p. 448) gives only that the normal subgroup is the normal closure of a finite set, and the passage to finite generation is Milnor's Lemma 3, which assumes the quotient polycyclic and uses the polycyclic normal form. As stated here the claim is true unless a finitely presented group of intermediate growth exists — the quotient inherits subexponential growth, and polynomial growth would make it virtually nilpotent by Gromov's theorem — so it is an open question rather than a target. The form Chou's proof uses and supplies is `Chou.fg_of_isVirtuallyPolycyclic_quotient`.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 400 (Milnor's Lemmas 1 and 2 as applied by Chou, with the remark on line 10 of Milnor p. 448)

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- Milnor's Lemmas 1 and 2 as used by Chou (p. 400, external): in a finitely generated
exponentially bounded group, a normal subgroup with finitely presented quotient is finitely
generated. -/
theorem fg_of_isFinitelyPresented_quotient {G : Type*} [Group G] [Group.FG G] (hb : IsExponentiallyBounded G)
    (N : Subgroup G) [N.Normal] [Group.IsFinitelyPresented (G ⧸ N)] : Group.FG N := by
  sorry

end Chou
