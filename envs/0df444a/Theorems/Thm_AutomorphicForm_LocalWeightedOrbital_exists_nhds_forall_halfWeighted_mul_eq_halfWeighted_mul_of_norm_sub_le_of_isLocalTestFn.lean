-- Prove2me | Theorems.Thm_AutomorphicForm_LocalWeightedOrbital_exists_nhds_forall_halfWeighted_mul_eq_halfWeighted_mul_of_norm_sub_le_of_isLocalTestFn
-- name    : AutomorphicForm.LocalWeightedOrbital.exists_nhds_forall_halfWeighted_mul_eq_halfWeighted_mul_of_norm_sub_le_of_isLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/d72b35d4-d4ba-5b2a-8b6f-6b6bed166c87
-- title:
--   Local constancy of the half-weighted orbital integral near t=1
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of its ring of integers, and equip the completion $K_v$ with a measurable structure that is the Borel structure; let $\mu$ be an additive Haar measure on $K_v$. Let $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ satisfy `IsLocalTestFn`, i.e. $f$ is locally constant and has compact support. Then, with $\mathrm{GL}_2(K_v)$ carrying the Borel $\sigma$-algebra `localGLBorel`, there are a neighbourhood $U$ of $1$ in $K_v^\times$ and a real $\rho > 0$ such that for all units $a, a', t, t'$ of $K_v$ with $t \in U$, $\|a' - a\| \le \rho\|a\|$ and $\|t' - t\| \le \rho\|1 - t\|$ one has the equality of `halfWeighted` values at $(a', a't')$ and at $(a, at)$. Here `halfWeighted`, formed with the norm $\|\cdot\|$ on $K_v$, the measure $\mu$, and the restriction of the Haar measure `localHaar` to `localIntegralSet` (the set of $g \in \mathrm{GL}_2(K_v)$ whose matrix and whose inverse matrix have all entries in the valuation ring), assigns to a pair $(a,b)$ of units the value $$-\sqrt{\|a\|/\|b\|}\int_{\{x \,:\, \|x\| > \|1 - b a^{-1}\|\}} \Big(\int f(\mathtt{arg}\,k\,a\,b\,x)\,dk\Big)\big(\log\|x\| - \log\|1 - ba^{-1}\|\big)\,d\mu(x),$$ the inner integral being over the restricted Haar measure and `arg` the project's $\mathrm{GL}_2$-valued function of $k$, $a$, $b$, $x$.
--
--   This is the local-constancy (germ) property of Langlands' half-weighted orbital integral $\tfrac12 A_1$ on the regular diagonal torus near the identity: for a locally constant compactly supported test function, the half-weighted integral at $\mathrm{diag}(a,at)$ depends only on the cell containing $(a,t)$ once $t$ is close to $1$. It is used in the comparison of matching local orbital integrals, being cited by the two statements on matching local data and their twisted counterparts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalWeightedOrbital_exists_nhds_forall_halfWeighted_mul_eq_halfWeighted_mul_of_norm_sub_le_of_isLocalTestFn.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.LocalWeightedOrbital.exists_nhds_forall_halfWeighted_mul_eq_halfWeighted_mul_of_norm_sub_le_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : MeasureTheory.Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f) :
    letI := AutomorphicForm.localGLBorel K v
    ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : v.adicCompletion K) - (a : v.adicCompletion K)‖ ≤ ρ * ‖(a : v.adicCompletion K)‖ →
        ‖(t' : v.adicCompletion K) - (t : v.adicCompletion K)‖ ≤ ρ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ →
        AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : v.adicCompletion K => ‖x‖) f a' (a' * t') =
        AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : v.adicCompletion K => ‖x‖) f a (a * t) := by sorry
