-- Prove2me | Theorems.Thm_EpochRamsey66_kalbfleisch_lower_bound
-- name    : EpochRamsey66.kalbfleisch_lower_bound
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T10:17:41.039557+00:00
-- url     : https://prove2.me/theorems/0ab01020-d7ba-46c9-990d-94d4c53a7aa2
-- title:
--   Kalbfleisch lower bound: a colouring of $K_{101}$ without monochromatic $K_6$
-- statement:
--   There exists a red–blue colouring of the edges of the complete graph on 101 vertices such that no set of exactly six vertices has all its edges red or all its edges blue. This is the construction underlying the known lower bound $R(6,6)\ge102$. The colouring is represented by a Boolean-valued function on pairs of vertices; the edge condition uses the canonical order $i<j$.
-- source:
--   J. G. Kalbfleisch, Chromatic Graphs and Ramsey's Theorem, Ph.D. thesis, University of Waterloo, January 1966; cited for R(6,6) ≥ 102 by Leaps in Bounds, https://leapsinbounds.org/constants/ramsey-6-6/

import Mathlib
import Definitions.Def_Ramsey55Types

namespace EpochRamsey66
theorem kalbfleisch_lower_bound :
    ∃ χ : Ramsey55.Coloring 101,
      ∀ S : Finset (Fin 101), S.card = 6 → ¬ Ramsey55.isMonochromatic χ S := by sorry
end EpochRamsey66
