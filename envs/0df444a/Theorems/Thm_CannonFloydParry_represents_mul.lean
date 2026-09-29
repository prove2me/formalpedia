-- Prove2me | Theorems.Thm_CannonFloydParry_represents_mul
-- name    : CannonFloydParry.represents_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:11:13.943842+00:00
-- url     : https://prove2.me/theorems/4ae8524d-cc3a-4dd1-a871-12c8eda9d637
-- title:
--   Tree diagrams compose
-- statement:
--   Let $Q$, $R$, $S$ be trees with a common number of leaves. If the tree diagram
--   $(Q,R)$ represents $f$ and the tree diagram $(R,S)$ represents $g$, then the tree diagram
--   $(Q,S)$ represents the composite that applies $f$ first and then $g$.
--
--   The middle tree must be literally the same in both diagrams. The composite is written $g \cdot
--   f$; in this group the product applies its right factor first, so $g \cdot f$ is $g \circ f$,
--   matching the source's $gf$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 222 (composition of tree diagrams)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem represents_mul {Q R S : TTree} {f g : UI ≃o UI}
    (hQR : Q.leafCount = R.leafCount) (hRS : R.leafCount = S.leafCount)
    (hf : Represents ⟨Q, R, hQR⟩ f) (hg : Represents ⟨R, S, hRS⟩ g) :
    Represents ⟨Q, S, hQR.trans hRS⟩ (g * f) := by
  sorry

end CannonFloydParry
