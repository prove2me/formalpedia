-- Prove2me | Theorems.Thm_Apery_delta_pos
-- name    : Apery.delta_pos
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T11:04:14.692982+00:00
-- url     : https://prove2.me/theorems/86c4c96e-7649-4d17-8374-90c79dd96428
-- title:
--   Strict positivity of the Hankel determinant at ζ(5)
-- statement:
--   For every positive natural number $n$,
--   $$\Delta_n(z_5)>0.$$
--   Here $\Delta_n$ is the determinant of the explicit $37n\times37n$ polynomial Hankel matrix. This establishes nonvanishing for the determinant used to construct small integer-polynomial values.
--
--   **Formalization Note** The source declaration `Apery.Δ_pos` is named `Apery.delta_pos` here to use an ASCII platform identifier; its assertion and hypotheses are unchanged.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Positivity.lean#L133-L134

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem delta_pos (n : ℕ) (hn : 0 < n) : 0 < aeval zeta5 (Δ n) := by sorry

end Apery
