-- Prove2me | Theorems.Thm_DefaultContagion_FinalSize_lemma_A_4
-- name    : DefaultContagion.FinalSize.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:22.417665+00:00
-- url     : https://prove2.me/theorems/fe16be81-2828-4ce1-8133-cddda3c9bcf7
-- title:
--   Lemma A.4, p. 32 — uniform convergence of the fluid functions and all derivatives
-- statement:
--   Let $f_\clubsuit^{(n)}$ be the five finite-economy fluid functions, formed from $\mu^{(n)},q^{(n)}$ and $\lambda^{(n)}$, and let $f_\clubsuit$ be their limiting counterparts. Under Assumptions 2, 3a and 3b, for each component $\clubsuit\in\{S,D,H^+,I^+,W\}$ and every integer $k\ge0$,
--   $$\sup_{0\le z\le1}\left|\frac{d^k}{dz^k}f_\clubsuit^{(n)}(z)-\frac{d^k}{dz^k}f_\clubsuit(z)\right|\longrightarrow0.$$
--   This gives the uniform derivative control required when the Gaussian limit is evaluated at a random time near the final stopping time.
--
--   **Formalization Note** The derivatives are ordinary iterated real derivatives, including at the endpoints by the analytic extension supplied by the degree moment assumption. The finite $I^+$ and $W$ functions use $\lambda^{(n)}$, correcting the printed $\lambda$.
-- source:
--   Amini, Cao & Sulem, arXiv:2104.00248v1, p. 32, Lemma A.4

import Mathlib
import Definitions.Def_DefaultContagion_FinalSize_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DefaultContagion.FinalSize

/-- Lemma A.4, p. 32: the five finite-economy fluid functions and every
order of derivative converge uniformly on the full unit interval. -/
theorem lemma_A_4 {X : Type*} [Countable X] [DecidableEq X]
    (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (qn : ℕ → X → ℕ → ℝ) (mu : X → ℝ) (q : X → ℕ → ℝ)
    (h2 : Assumption2 dp typ qn mu q)
    (h3a : Assumption3a dp dm typ mu)
    (h3b : Assumption3b dp dm typ) :
    let lam : ℝ := ∑' x, mu x * (dp x : ℝ)
    ∀ c : Fin 5, ∀ k : ℕ,
      TendstoUniformlyOn
        (fun n z => iteratedDeriv k
          (fun w => fVec dp dm (lamN dp typ n) (muN typ n) (qn n) w c) z)
        (fun z => iteratedDeriv k (fun w => fVec dp dm lam mu q w c) z)
        atTop (Set.Icc (0 : ℝ) 1) := by sorry

end DefaultContagion.FinalSize
