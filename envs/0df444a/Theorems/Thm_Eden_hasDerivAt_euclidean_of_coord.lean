-- Prove2me | Theorems.Thm_Eden_hasDerivAt_euclidean_of_coord
-- name    : Eden.hasDerivAt_euclidean_of_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:31.083802+00:00
-- url     : https://prove2.me/theorems/4e750527-9724-4431-a403-cbd291921911
-- title:
--   Eden: has Deriv At euclidean of coord
-- statement:
--   Coordinate derivatives assemble into the Euclidean vector derivative.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Evolution.lean#L31-L38
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Evolution.lean#L31-L38

import Definitions.Def_Eden_PlanarFlow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Definitions.Def_Eden_Evolution
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_euclidean_of_coord {n : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin n)} {v : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : ∀ i, HasDerivAt (fun τ => f τ i) (v i) t) : HasDerivAt f v t := by sorry
