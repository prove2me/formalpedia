-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_Supplement_theorem_13_c_counterexample
-- name    : DataDrivenRO.Guarantee.Supplement.theorem_13_c_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:50:41.933297+00:00
-- url     : https://prove2.me/theorems/31b248aa-4fae-4854-b8d6-05d63e634d92
-- title:
--   Theorem 13(c) (corrected: positive-radius counterexamples to convexity in ε)
-- statement:
--   Take one-dimensional scenarios $(0,1)$, empirical probabilities $(1/2,1/2)$, direction $v=1$, chi-square radius $1/6$ and G-test radius $\tfrac12\log(4/3)>0$. For either of the two published uncertainty-set families, all sets at $0<\epsilon<1$ are nonempty compact convex, and
--   $$
--   h(\epsilon)=\delta^*(1\mid U_\epsilon)=\min\{1,3/(4\epsilon)\}.
--   $$
--   The function is not convex on $(0,1)$, since
--   $$
--   h(3/4)=1>13/14=\tfrac12h(5/8)+\tfrac12h(7/8).
--   $$
--   These two valid instances refute the universal assertion over five families in the function-convexity reading of Theorem 13(c). They do not refute convexity of the epigraph in $(v,t)$, nor convexity of fixed-$t$ sublevel sets in $\epsilon$. Those are different claims. No statement about the remaining three families is needed to refute the universal conjunction, and no case has been silently removed from an asserted version of the original theorem.
--
--   Differences from the source:
--   - correction: Theorem 13(c) asserts convexity in epsilon for all five families → two explicit positive-radius counterexamples to the function-convexity claim using the published chi-square and G sets; reason: the source proof on PDF 47 incorrectly infers convexity after an infimum; the midpoint values 1,1,6/7 contradict convexity and the original universal claim is false
--   - reading: bi-convex constraint in (v,t) and epsilon → ConvexOn of epsilon ↦ supportFunction at v=1, following the published 13(a)/(b) reading and the structured brief; reason: the proof on PDF 47 explicitly argues function convexity; fixed-t sublevel convexity is weaker and is not refuted by this example
--   - encoding: two scenarios in R and positive test radii → Fin 2 scenarios in Fin 1 → R, with radii 1/6 and log(4/3)/2; reason: both confidence regions have maximal upper-scenario probability 3/4; no zero-radius or empty-set boundary is used
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 13(c), p. 29; EC.1.8, p. ec9 (PDF 47); (10), (12)–(13), pp. 12–13

import Mathlib
import Definitions.Def_DataDrivenRO_Discrete_Setting

namespace DataDrivenRO.Guarantee.Supplement

/-- Positive-radius counterexamples to the function-convexity reading of Theorem 13(c).
Each confidence region has largest second probability 3/4. Both support functions are
min(1,3/(4ε)), which violates the convexity inequality at 5/8, 3/4, 7/8. -/
theorem theorem_13_c_counterexample :
    let a : Fin 2 → (Fin 1 → ℝ) := fun j _ => if j = 0 then 0 else 1
    let phat : Fin 2 → ℝ := fun _ => 1 / 2
    let rhoG : ℝ := Real.log (4 / 3) / 2
    let Uchi : ℝ → Set (Fin 1 → ℝ) := DataDrivenRO.Discrete.Uchi2 a phat (1 / 6)
    let Ug : ℝ → Set (Fin 1 → ℝ) := DataDrivenRO.Discrete.UG a phat rhoG
    phat ∈ stdSimplex ℝ (Fin 2) ∧ 0 < rhoG ∧
    (∀ U : ℝ → Set (Fin 1 → ℝ), U = Uchi ∨ U = Ug →
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        (U ε).Nonempty ∧ IsCompact (U ε) ∧ Convex ℝ (U ε) ∧
        RobustMDP.Shared.supportFunction (U ε) (fun _ => 1) = min 1 (3 / (4 * ε))) ∧
      RobustMDP.Shared.supportFunction (U (3 / 4)) (fun _ => 1) >
        (1 / 2 : ℝ) * RobustMDP.Shared.supportFunction (U (5 / 8)) (fun _ => 1) +
        (1 / 2 : ℝ) * RobustMDP.Shared.supportFunction (U (7 / 8)) (fun _ => 1) ∧
      ¬ ConvexOn ℝ (Set.Ioo (0 : ℝ) 1)
        (fun ε => RobustMDP.Shared.supportFunction (U ε) (fun _ => 1))) := by sorry

end DataDrivenRO.Guarantee.Supplement
