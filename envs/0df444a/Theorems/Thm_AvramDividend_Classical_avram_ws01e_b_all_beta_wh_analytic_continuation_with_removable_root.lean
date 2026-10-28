-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root
-- name    : AvramDividend.Classical.avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:17:23.970353+00:00
-- url     : https://prove2.me/theorems/57a0f80e-734f-42c3-b98d-e49ce403ce32
-- title:
--   All-positive-beta Wiener–Hopf analytic continuation with an explicitly removable root
-- statement:
--   Let L be an analytic candidate descending Laplace transform and g an analytic shifted spectrally negative Lévy exponent on all β>0, with g(λ)=p, positive simple derivative m=g'(λ), and no other positive solution of g(β)=p. If the exact crossed Wiener–Hopf factor L(β)(p−g(β))=(p/λ)(λ−β) holds on the genuinely integrable strip 0<β<λ, then it holds by analytic identity throughout β>0 and yields the un-crossed full descending factor L(β)=(p/λ)(λ−β)/(p−g(β)) away from the unique root, and the actual removable value L(λ)=p/(λ m). This bridge never divides a divergent positive exponential moment beyond its strip. The analyticity and initial strip identity remain explicit hypotheses to be established for the actual Qp path law.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013) §2.1–2.2 equation (2.7), Corollary 2.2 analytic-extension argument. Pinned Mathlib AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq on connected Ioi 0, analyticity under products/subtractions, and derivative uniqueness at λ. Publication repair: reserved λ binder renamed to lam throughout formal statement.

import Mathlib
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open MeasureTheory Set Filter
open scoped Topology

theorem AvramDividend.Classical.avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root
    (p lam m : ℝ) (hp : 0 < p) (hlam : 0 < lam) (hm : 0 < m)
    (L g : ℝ → ℝ)
    (hLAnalytic : AnalyticOnNhd ℝ L (Set.Ioi (0 : ℝ)))
    (hgAnalytic : AnalyticOnNhd ℝ g (Set.Ioi (0 : ℝ)))
    (hgRoot : g lam = p) (hgDeriv : HasDerivAt g m lam)
    (hgUnique : ∀ β : ℝ, 0 < β → β ≠ lam → g β ≠ p)
    (hStrip : ∀ β : ℝ, 0 < β → β < lam →
      L β * (p - g β) = (p / lam) * (lam - β)) :
    ∀ β : ℝ, 0 < β →
      L β = if β = lam then p / (lam * m)
        else (p / lam) * ((lam - β) / (p - g β)) := by sorry
