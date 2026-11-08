-- Prove2me | Theorems.Thm_DegreeSensitivity_degree_five_full_sensitivity
-- name    : DegreeSensitivity.degree_five_full_sensitivity
-- status  : Open
-- author  : @queelius
-- created : 2026-11-07T16:52:22.348208+00:00
-- url     : https://prove2.me/theorems/5a152163-29c9-40bf-8ef9-5e4a05f59025
-- title:
--   A degree-five function fully sensitive on fourteen variables (open)
-- statement:
--   Some Boolean function $g$ on 14 bits has degree at most 5, $g(\mathbf 0) = 0$ and $g(e_i) = 1$ for all $i$.
-- source:
--   Open; the smallest base not excluded by Amano (2010), named in the Epoch statement, "State of the art". Partial conditional computer evidence: A. R. Towell, Zenodo doi:10.5281/zenodo.23999933 (exclusions of many Fourier sign patterns; settles neither this statement nor its negation).

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree

namespace DegreeSensitivity

theorem degree_five_full_sensitivity :
    ∃ g : BoolFunc 14, polyDegree g ≤ 5 ∧ g (fun _ => false) = false ∧
      ∀ i : Fin 14, g (Function.update (fun _ => false) i true) = true := by sorry

end DegreeSensitivity
