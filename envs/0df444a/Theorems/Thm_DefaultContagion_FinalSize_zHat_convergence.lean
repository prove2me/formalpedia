-- Prove2me | Theorems.Thm_DefaultContagion_FinalSize_zHat_convergence
-- name    : DefaultContagion.FinalSize.zHat_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:12.08963+00:00
-- url     : https://prove2.me/theorems/57f2e6ec-46eb-42e2-9ed0-12074bb2dbb1
-- title:
--   Proof of Theorem 3.7 (§A.8), p. 41 — convergence of the finite-economy largest zero
-- statement:
--   Let $z^*$ be the largest zero of $f_W$ on $[0,1]$, and let $\widehat z_n$ be the largest zero of the finite-economy function $f_W^{(n)}$ on that interval. Under Assumptions 2, 3a and 3b, if $0<z^*\le1$ and $f_W'(z^*)>0$, then
--   $$\widehat z_n\longrightarrow z^*.$$
--   Moreover, for each $\varepsilon>0$, the finite-economy function $f_W^{(n)}$ is strictly positive throughout $[z^*+\varepsilon,1]$ for all sufficiently large $n$. The latter property identifies $\widehat z_n$ as the largest zero near $z^*$ and is used in the final-size expansion.
--
--   **Formalization Note** When $z^*+\varepsilon>1$, the interval is empty and its positivity clause is automatic; the convergence claim remains substantive. The finite $f_W^{(n)}$ uses $\lambda^{(n)}$.
-- source:
--   Amini, Cao & Sulem, arXiv:2104.00248v1, p. 41, proof of Theorem 3.7 (§A.8)

import Mathlib
import Definitions.Def_DefaultContagion_FinalSize_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DefaultContagion.FinalSize

/-- The unnumbered zero-location argument in the proof of Theorem 3.7,
§A.8, p. 41. -/
theorem zHat_convergence {X : Type*} [Countable X] [DecidableEq X]
    (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (qn : ℕ → X → ℕ → ℝ) (mu : X → ℝ) (q : X → ℕ → ℝ)
    (h2 : Assumption2 dp typ qn mu q)
    (h3a : Assumption3a dp dm typ mu)
    (h3b : Assumption3b dp dm typ) :
    let lam : ℝ := ∑' x, mu x * (dp x : ℝ)
    let zStar := lastZero (fW dp dm lam mu q)
    let zHat : ℕ → ℝ := fun n =>
      lastZero (fW dp dm (lamN dp typ n) (muN typ n) (qn n))
    0 < zStar → zStar ≤ 1 → 0 < deriv (fW dp dm lam mu q) zStar →
      Tendsto zHat atTop (𝓝 zStar) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ z ∈ Set.Icc (zStar + ε) 1,
          0 < fW dp dm (lamN dp typ n) (muN typ n) (qn n) z := by sorry

end DefaultContagion.FinalSize
