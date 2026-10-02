-- Prove2me | Theorems.Thm_CarrollGR_vacuum_einstein_eq_iff_ricci_zero
-- name    : CarrollGR.vacuum_einstein_eq_iff_ricci_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:14:10.174437+00:00
-- url     : https://prove2.me/theorems/2e530cec-c4d2-4b4f-b443-2432ee84bc4e
-- title:
--   Vacuum Einstein equation: $R_{\mu\nu}=0$
-- statement:
--   Let $g_{\mu\nu}(x)$ have signature $(-+++)$ at a point $x$ and let $G$ be a real constant. In vacuum, $T_{\mu\nu}=0$, Einstein's equation at $x$ holds if and only if
--
--   $$R_{\mu\nu}=0\qquad\text{for all }\mu,\nu .$$
--
--   This is Einstein's equation in vacuum, the equation solved by the Schwarzschild metric.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 16, eq. (69)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem vacuum_einstein_eq_iff_ricci_zero (g : TensorField2) (GN : ℝ) (x : Coord)
    (hg : IsLorentzian (g x)) :
    EinsteinEq g GN (fun _ => 0) x ↔ ∀ μ ν : Fin 4, ricci g μ ν x = 0 := by sorry

end CarrollGR
