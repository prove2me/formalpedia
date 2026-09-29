-- Prove2me | Theorems.Thm_CannonFloydParry_exists_isNormalFormData
-- name    : CannonFloydParry.exists_isNormalFormData
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:12:44.757625+00:00
-- url     : https://prove2.me/theorems/30608237-faa7-406c-95ef-ba69dca16e72
-- title:
--   Normal-form data for a reduced tree diagram
-- statement:
--   If a reduced tree diagram represents an element $f \ne 1$ of $F$, then there are two
--   lists of nonnegative integers $a$ and $b$, of the same nonempty length, satisfying the normal
--   form conditions — exactly one of the last entries is nonzero, and if $a_k$ and $b_k$ are both
--   positive for some $k$ before the last index then $a_{k+1}$ or $b_{k+1}$ is positive — such that
--   $$f = X_0^{b_0} \cdots X_n^{b_n} \, X_n^{-a_n} \cdots X_0^{-a_0}.$$
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 pp. 223-224 (the step from Theorem 2.5 to Corollary-Definition 2.7)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem exists_isNormalFormData {d : TreeDiagram} {f : UI ≃o UI}
    (hd : IsReduced d) (hr : Represents d f) (hne : f ≠ 1) :
    ∃ as bs : List ℕ, IsNormalFormData as bs ∧ f = word bs * (word as)⁻¹ := by
  sorry

end CannonFloydParry
