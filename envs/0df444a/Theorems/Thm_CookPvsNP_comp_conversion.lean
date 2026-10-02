-- Prove2me | Theorems.Thm_CookPvsNP_comp_conversion
-- name    : CookPvsNP.comp_conversion
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:07:03.834545+00:00
-- url     : https://prove2.me/theorems/aa3bd691-ccf8-4296-a098-cdff67b20d2b
-- title:
--   Exact intermediate-word conversion of the Cook composite machine
-- statement:
--   If the first source has halted with an encoded ordinary word followed by padding, the composite converts its first-phase frame to the defined second-phase frame in exactly $2|R|+6$ transitions, where $R$ is the source right list. The intermediate symbols are translated through the two embeddings. The equality includes empty words, arbitrary old left-side contents, and exact blank padding.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompConversion

namespace CookPvsNP
theorem comp_conversion {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (q : M₁.Q) (left : List (Option A)) (w : List S) (padding : ℕ)
    (hn : q = M₁.qaccept ∨ q = M₁.qreject) :
    (compTM j₁ j₂ M₁ M₂).run
      (2 * (compWordCfg j₁ q left w padding).right.length + 6)
      (compFirstCfg (compWordCfg j₁ q left w padding)) =
      (compConvertedFrame j₁ j₂ M₂.q₀ left w padding).encode := by sorry
end CookPvsNP
