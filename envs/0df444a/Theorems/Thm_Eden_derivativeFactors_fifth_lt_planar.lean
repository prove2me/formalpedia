-- Prove2me | Theorems.Thm_Eden_derivativeFactors_fifth_lt_planar
-- name    : Eden.derivativeFactors_fifth_lt_planar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:29:49.722006+00:00
-- url     : https://prove2.me/theorems/20534bc0-e7f7-5ea1-a4aa-76ada4db4d91
-- title:
--   Eden: derivative Factors fifth lt planar
-- statement:
--   On A, at positive time and c>4, each of the four planar entries of the ambient
--   orthogonal factorisation strictly exceeds its fifth entry. The planar entries
--   here are in block order, not descending order.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L31-L34
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L31-L34

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.derivativeFactors_fifth_lt_planar {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4) :
    derivativeFactors c t p 4 < derivativeFactors c t p i.castSucc := by sorry
