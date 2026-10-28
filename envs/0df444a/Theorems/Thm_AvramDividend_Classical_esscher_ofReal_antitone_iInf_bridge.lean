-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ofReal_antitone_iInf_bridge
-- name    : AvramDividend.Classical.esscher_ofReal_antitone_iInf_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:44:59.789129+00:00
-- url     : https://prove2.me/theorems/17abb413-51d1-4813-af4c-c6651a41eeed
-- title:
--   Antitone finite-horizon real infima commute with ENNReal.ofReal at the limit
-- statement:
--   For any real-valued antitone function f on NNReal with finite real limit L as time tends to infinity, the ENNReal infimum of ofReal(f(t)) over all horizons equals ofReal(L). This rigorously connects the already-Proved Esscher survival-mass real iInf limit to the canonical perpetual infimum probability CDF expressed in ENNReal. It assumes neither the Wiener–Hopf transform nor any Esscher process path-law extension.
-- source:
--   Pinned Mathlib Topology.Order.MonotoneConvergence tendsto_atTop_iInf, ENNReal.continuous_ofReal and ENNReal.ofReal_le_ofReal, plus Prove2Me accepted source-specific Esscher survival antitone and real iInf-limit 6335f5be and 9752e377.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.ENNReal.Real

open Filter

theorem AvramDividend.Classical.esscher_ofReal_antitone_iInf_bridge
    (f : NNReal → ℝ) (L : ℝ)
    (hanti : Antitone f)
    (hlim : Tendsto f atTop (nhds L)) :
    (⨅ t : NNReal, ENNReal.ofReal (f t)) = ENNReal.ofReal L := by sorry
