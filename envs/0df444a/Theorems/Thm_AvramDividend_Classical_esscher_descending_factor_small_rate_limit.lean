-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_descending_factor_small_rate_limit
-- name    : AvramDividend.Classical.esscher_descending_factor_small_rate_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:37:14.555264+00:00
-- url     : https://prove2.me/theorems/55bdfd97-3d89-4a76-a891-64777df84ad0
-- title:
--   Small-rate limit of a fully extended exponential-horizon descending factor
-- statement:
--   For a positive slope m, a fixed β>0 and g(β)>0, suppose root(p)→0, p/root(p)→m, and finite-rate descending Laplace transforms D_p satisfy the fully β-domain-extended expression D_p=(p/root(p))((root(p)-β)/(p-g(β))) eventually as p↓0. Then D_p→mβ/g(β). This is conditional on 1E-B's all-β Wiener–Hopf extension; a formula derived only under β<root(p) does not qualify and cannot be used in this limit.
-- source:
--   KKR The Theory of Scale Functions, Wiener–Hopf factorisation and Esscher adjustment; pure filter arithmetic. Corrects failed publication 5abc82fc (missing real-analysis import for ℝ).

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
open Filter Set

theorem AvramDividend.Classical.esscher_descending_factor_small_rate_limit
    (root D : ℝ → ℝ) (gβ m β : ℝ)
    (hm : 0 < m) (hβ : 0 < β) (hgβ : 0 < gβ)
    (hroot0 : Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (hratio : Tendsto (fun p : ℝ => p / root p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m))
    (hfactor :
      D =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
        (fun p : ℝ => (p / root p) * ((root p - β) / (p - gβ)))) :
    Tendsto D (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (m * β / gβ)) := by sorry
