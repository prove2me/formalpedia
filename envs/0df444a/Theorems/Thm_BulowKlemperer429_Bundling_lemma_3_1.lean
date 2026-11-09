-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_lemma_3_1
-- name    : BulowKlemperer429.Bundling.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:08.982907+00:00
-- url     : https://prove2.me/theorems/2bc32040-da96-4309-a4d4-a6284bd85448
-- title:
--   Lemma 3.1 — joint concavity and coordinate bounds for w
-- statement:
--   Let $M$ be a feasible, truthful, individually rational mechanism with measurable payment and nonnegative prices. For every nonnegative value vector $v$, let $w(v)$ be total value minus utility. Then $w$ is jointly concave on the closed nonnegative orthant. For every coordinate $j$, its slice $g(z)=w(v_{-j},z)$ is nondecreasing and $1$-Lipschitz on $[0,\infty)$, and
--   $$g'_+(v_j)\le1-x_j(v).$$
--   The right derivative exists at every such point, including $v_j=0$.
--
--   The statement connects truthful allocations to the shape of residual value. Joint concavity is part of the conclusion, not merely separate concavity of the slices.
--
--   Differences from the source:
--   - encoding: closed truthful individually rational menus → feasible IC and IR direct mechanisms on the entire nonnegative orthant with measurable payment; reason: the direct mechanism records the selected option at every type; lotteries are allowed and no allocation measurability is imposed
--   - encoding: right derivatives on [0,∞), including zero → derivWithin g (Ioi x) x, with existence stated explicitly; reason: concavity and the Lipschitz bound give the right derivative everywhere on the half-line; the extension below zero is unused
--   - encoding: joint concavity of w on the nonnegative orthant → ConcaveOn over real vectors with every coordinate nonnegative; reason: residualReal agrees with w there; arbitrary values of its extension outside the orthant are unused
--   - generalization: the surrounding argument first considers bounded w → the shape conclusion holds without bounding w; reason: the proof of Lemma 3.1 uses feasibility and truthfulness only, so this includes every bounded menu considered in the source
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 8, Lemma 3.1 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Residual
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

theorem lemma_3_1 {ι : Type} [Fintype ι]
    (M : MultiItemRev.BundlingOpt.Mechanism ι)
    (hM : MultiItemRev.BundlingOpt.IsAdmissible M)
    (hNPT : MultiItemRev.BundlingOpt.IsNPT M) :
    ConcaveOn ℝ {v : ι → ℝ | ∀ j, 0 ≤ v j} (residualReal M) ∧
    (∀ v j, MonotoneOn (residualSlice M v j) (Set.Ici 0)) ∧
    (∀ v j, LipschitzOnWith 1 (residualSlice M v j) (Set.Ici 0)) ∧
    (∀ v j, HasDerivWithinAt (residualSlice M v j)
        (rightDeriv (residualSlice M v j) (v j : ℝ)) (Set.Ioi (v j : ℝ)) (v j : ℝ) ∧
      rightDeriv (residualSlice M v j) (v j : ℝ) ≤ 1 - M.q v j) := by sorry

end BulowKlemperer429.Bundling
