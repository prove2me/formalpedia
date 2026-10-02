-- Prove2me | Theorems.Thm_CookPvsNP_comp_output_form
-- name    : CookPvsNP.comp_output_form
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:07:54.613379+00:00
-- url     : https://prove2.me/theorems/a3854fbf-cf59-4650-a65e-e7d2c1d245bc
-- title:
--   Recover a finite word configuration from an ordinary machine output
-- statement:
--   If the output of a Cook machine configuration is an ordinary encoded word, its head and right list consist exactly of that word followed by explicit blank padding. There exists a padding length giving equality with the finite word configuration. State and left-side contents are preserved, and the empty word is included.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompConversion

namespace CookPvsNP
theorem comp_output_form {I Γ : Type} (ι : I ↪ Γ) (M : TM Γ) (c : Cfg Γ M.Q) (w : List I)
    (hout : M.output c = w.map (some ∘ ι)) :
    ∃ padding, c = compWordCfg ι c.state c.left w padding := by sorry
end CookPvsNP
