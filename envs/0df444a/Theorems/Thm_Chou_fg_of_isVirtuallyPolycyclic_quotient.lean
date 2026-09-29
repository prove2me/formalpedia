-- Prove2me | Theorems.Thm_Chou_fg_of_isVirtuallyPolycyclic_quotient
-- name    : Chou.fg_of_isVirtuallyPolycyclic_quotient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T12:44:03.651969+00:00
-- url     : https://prove2.me/theorems/b93cd965-a81e-4b33-bd56-3ce758cdc545
-- title:
--   Milnor's Lemmas 1 to 3 in the form Chou uses them: in a finitely generated exponentially bounded group, a normal subgroup with virtually polycyclic quotient is finitely generated
-- statement:
--   Let $G$ be a finitely generated group which is exponentially bounded, and let $N$ be a
--   normal subgroup such that the quotient $G/N$ has a polycyclic subgroup of finite index. Then $N$ is
--   finitely generated.
--
--   Chou writes, on p. 400, "Now $C$ is finitely presented … By applying Lemmas 1 and 2 of Milnor we
--   conclude that $A$ is finitely generated". Milnor's Lemma 2 concludes only that the normal subgroup
--   is the normal closure of finitely many elements; the step to finite generation is Lemma 3,
--   which assumes the quotient polycyclic and uses that to write each conjugating element as a product
--   $\beta_1^{i_1} \cdots \beta_p^{i_p}$, so that applying Lemma 1 once per generator terminates. The
--   hypothesis here is the one that step needs and the one Chou's own application supplies, the
--   quotient there being almost nilpotent. No finite presentation is required.
--
--   Being virtually polycyclic is written out as the existence of a finite-index subgroup of $G/N$
--   satisfying the published definition of a polycyclic group, a subnormal series with cyclic
--   quotients.
-- source:
--   Milnor, J., Growth of finitely generated solvable groups, Journal of Differential Geometry 2 (1968) 447–449, https://doi.org/10.4310/jdg/1214428659, Lemmas 1 and 2 (p. 448) and Lemma 3 (pp. 448–449), with the abelian hypothesis on the normal subgroup removed and stated for the virtually polycyclic quotient that Lemma 3's proof requires; applied in this form in Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 400, proof of Lemma 3.1, where the quotient is almost nilpotent

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Chou

/-- Milnor's Lemmas 1 to 3 in the form his proof actually supplies, and in the form Chou's §3 uses:
in a finitely generated exponentially bounded group, a normal subgroup whose quotient is virtually
polycyclic is finitely generated.

Chou writes on p. 400 "Now `C` is finitely presented … By applying Lemmas 1 and 2 of Milnor [17] we
conclude that `A` is finitely generated". Milnor's Lemma 2 (p. 448) concludes only that the normal
subgroup is the normal closure of a finite set; the passage to finite generation is his Lemma 3
(p. 448), which is stated for a polycyclic quotient, and its proof (p. 449) uses the polycyclic
normal form to write each conjugate as a conjugate by `β₁^{i₁} ⋯ β_p^{i_p}`, which is what makes
the induction finite. Chou applies the result to an almost nilpotent quotient, so the hypothesis
here is the one his use supplies and the one Milnor's argument needs; no finite presentation is
required. "Virtually polycyclic" is written out as a finite-index subgroup satisfying the published
`MilnorWolf.IsPolycyclic`. -/
theorem fg_of_isVirtuallyPolycyclic_quotient {G : Type*} [Group G] [Group.FG G]
    (hb : IsExponentiallyBounded G) (N : Subgroup G) [N.Normal]
    (hq : ∃ H : Subgroup (G ⧸ N), H.FiniteIndex ∧ MilnorWolf.IsPolycyclic H) :
    Group.FG N := by
  sorry

end Chou
