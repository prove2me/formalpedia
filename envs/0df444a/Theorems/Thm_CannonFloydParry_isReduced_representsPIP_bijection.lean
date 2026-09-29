-- Prove2me | Theorems.Thm_CannonFloydParry_isReduced_representsPIP_bijection
-- name    : CannonFloydParry.isReduced_representsPIP_bijection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:10:03.964278+00:00
-- url     : https://prove2.me/theorems/0474ac9f-135e-4515-9acc-17613747dfa9
-- title:
--   p. 253 — PIP⁺ of [0,1] corresponds bijectively to reduced tree diagrams
-- statement:
--   Reading the tree diagrams of §2 on the tree $\mathcal{T}'$ of integral subsimplices instead of the dyadic tree: every PIP⁺ map of $[0,1]$ is represented by exactly one reduced tree diagram; every reduced tree diagram represents exactly one order isomorphism of $[0,1]$; and every order isomorphism represented by any tree diagram is a PIP⁺ map of $[0,1]$.
--
--   **Formalization Note.** $PIP^+(\Delta_1)$ is taken in its model on $[0,1]$ (`PIPPlus01Set`), where the source proves it; the isomorphism with $PIP^+(\Delta_1)$ is the p. 251 milestone.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 253, tree diagrams for PIP⁺(Δ₁)

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem isReduced_representsPIP_bijection :
    (∀ f ∈ PIPPlus01Set, ∃! d : TreeDiagram, IsReduced d ∧ RepresentsPIP d f) ∧
      (∀ d : TreeDiagram, IsReduced d → ∃! f : UI ≃o UI, RepresentsPIP d f) ∧
      ∀ (d : TreeDiagram) (f : UI ≃o UI), RepresentsPIP d f → f ∈ PIPPlus01Set := by
  sorry

end CannonFloydParry
