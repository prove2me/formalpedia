-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_Supplement_lemma_3_9
-- name    : AccelNewtonDinkelbach.Supplement.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:03:08.510874+00:00
-- url     : https://prove2.me/theorems/1590a482-2a8b-4e95-b22c-c56e9cf96359
-- title:
--   Lemma 3.9 — the largest root is the attained fractional optimum, or the value is $-\infty$
-- statement:
--   In the setting of $(F)$, assume there are $\delta'\in\operatorname{dom}(f)$ and $x'\in D$ with $d^\top x'>0$ such that $f(\delta')=(c-\delta'd)^\top x'\le0$. If $f$ has a root, its roots have a greatest member $\delta^*$, the value of $(F)$ is $\delta^*$, and a feasible point attains that ratio. If $f$ has no root, the value of $(F)$ is $-\infty$.
--
--   Differences from the source:
--   - encoding: f and the value of (F) take values in R ∪ {−∞} → both values are EReal and membership in dom(f) excludes ⊥; reason: this preserves the finite and unbounded cases without a default real infimum
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 3.9, p.10

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_LinearFractionalProgram

namespace AccelNewtonDinkelbach.Supplement

open LinearFractionalProgram

set_option autoImplicit false

/-- **Lemma 3.9 (largest root and attainment).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 3.9, p.10.

The hypothesis records exactly the attained, nonpositive finite parametric value at `δ'`.
If a root exists, the root set has a greatest member, the fractional value equals it, and a
feasible point attains it.  If no root exists, the fractional value is `−∞`. -/
theorem lemma_3_9 {m : ℕ} (P : LinearFractionalProgram m) (hpoly : P.IsPolyhedron)
    (hfeas : ∃ x, P.Feasible x) (δ' : ℝ) (x' : Fin m → ℝ)
    (hδ' : δ' ∈ P.paramDom) (hx'D : x' ∈ P.D) (hden : 0 < dot P.d x')
    (hatt : P.paramValue δ' = ((dot P.c x' - δ' * dot P.d x' : ℝ) : EReal))
    (hnonpos : dot P.c x' - δ' * dot P.d x' ≤ 0) :
    ((P.roots.Nonempty →
        ∃ δstar : ℝ, IsGreatest P.roots δstar ∧ P.value = (δstar : EReal) ∧
          ∃ x, P.Attains x ∧ dot P.c x / dot P.d x = δstar) ∧
      (¬ P.roots.Nonempty → P.value = ⊥)) := by sorry

end AccelNewtonDinkelbach.Supplement
