-- Prove2me | Theorems.Thm_EdenVerified_p20_singularValues_on_torus
-- name    : EdenVerified.p20_singularValues_on_torus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:21.675753+00:00
-- url     : https://prove2.me/theorems/765fd3fa-dbca-51ee-9918-1e22587a7a76
-- title:
--   Eden Verified: p20 singular Values on torus
-- statement:
--   The Eden Verified construction uses the p20 singular Values on torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1615-L1620
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1615-L1620

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p20_singularValues_on_torus :
    ∀ {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus),
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      ![Real.exp (2 * t), Real.exp (2 * t), 1, 1, Real.exp (-c * t)] := by sorry
