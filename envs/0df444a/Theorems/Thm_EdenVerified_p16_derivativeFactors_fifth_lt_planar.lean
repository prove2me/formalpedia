-- Prove2me | Theorems.Thm_EdenVerified_p16_derivativeFactors_fifth_lt_planar
-- name    : EdenVerified.p16_derivativeFactors_fifth_lt_planar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:32.340497+00:00
-- url     : https://prove2.me/theorems/16223be5-3bdb-4136-be75-136d1bdfd768
-- title:
--   Eden Verified: p16 derivative Factors fifth lt planar
-- statement:
--   The Eden Verified construction uses the p16 derivative Factors fifth lt planar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1508-L1512
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1508-L1512

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p16_derivativeFactors_fifth_lt_planar :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4),
    derivativeFactors c t p 4 < derivativeFactors c t p i.castSucc := by sorry
