-- Prove2me | Theorems.Thm_Apery_ccount_cc
-- name    : Apery.ccount_cc
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:09:31.438536+00:00
-- url     : https://prove2.me/theorems/2f59139f-5470-4a62-8dd8-59a181ba447e
-- title:
--   The nine continuous interval counts: $c_{ij}(f,g)$ for $f,g \in [0,1)$
-- statement:
--   For fractional parts $f, g \in [0,1)$, the nine continuous interval counts $c_{ij}(f,g) = \max\bigl(0, \min(\min(\mathrm{cvHi}_f(i), \mathrm{cvHi}_g(j)), \tfrac12) - \max(\max(\mathrm{cvLo}_f(i), \mathrm{cvLo}_g(j)), 0)\bigr)$ take the explicit values $c_{00} = 1/2$, $c_{01} = \min(g, 1/2)$, $c_{02} = \max(0, g - 1/2)$, $c_{10} = \min(f, 1/2)$, $c_{20} = \max(0, f - 1/2)$, $c_{11} = \min(\min f g, 1/2)$, $c_{12} = \max(0, \min(f,1/2) + g - 1)$, $c_{21} = \max(0, \min(g,1/2) + f - 1)$, $c_{22} = \max(0, \min(f,g) - 1/2)$. This bundles the nine lemmas `cc00`..`cc22` of `Apery/Growth/TableGen.lean` (which every piece of the inner/outer tables uses); it is stated as a single bundle to keep the generated-table decompositions reasonably sized. **Formalization Note** `ccount`, `cvLo`, `cvHi` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/TableGen.lean#L42-L103

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem ccount_cc {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) :
    ccount f g 0 0 = 1 / 2 ∧
    ccount f g 0 1 = min g (1 / 2) ∧
    ccount f g 0 2 = max 0 (g - 1 / 2) ∧
    ccount f g 1 0 = min f (1 / 2) ∧
    ccount f g 2 0 = max 0 (f - 1 / 2) ∧
    ccount f g 1 1 = min (min f g) (1 / 2) ∧
    ccount f g 1 2 = max 0 (min f (1 / 2) + g - 1) ∧
    ccount f g 2 1 = max 0 (min g (1 / 2) + f - 1) ∧
    ccount f g 2 2 = max 0 (min f g - 1 / 2) := by
  sorry

end Apery
