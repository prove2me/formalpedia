-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_theorem_3_7
-- name    : ExactLearningSeparation678.Randomized.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:33.216837+00:00
-- url     : https://prove2.me/theorems/dae2ad42-da7a-43c0-ae55-24ce7dbf1d5e
-- title:
--   Theorem 3.7 — randomized query lower bound
-- statement:
--   For the classes $C_t$ of Definition 3.1, with $t=2^m$ and $m\ge2$,
--   $$R(C_t)=\Omega(t^3).$$
--   Quantitatively, there is an absolute $m_0$ such that $R(C_t)>t^3/10$ for all $m\ge m_0$. For every parameter and every deterministic learner using at most $D$ queries, retain Eq. (16):
--   $$\Pr_\mu[\mathrm{success}]\le\frac{D+1}{t^6}+\frac{\binom D2}{t^6}+\binom Dt(2/t^2)^t.$$
--   For all $m\ge m_0$ and integer budgets $D\le t^3/10$, the collision term is at most $1/200$, the final term is at most $(e/5)^t$, and the success probability is strictly less than $2/3$.
--
--   The conclusion concerns the actual minimum worst-case randomized query budget. The distributional estimates quantify over every deterministic learner and do not assume any lower bound on the complexity.
--
--   **Formalization Note** Integer budgets implement $\lfloor t^3/10\rfloor$ without treating $t^3/10$ as an integer. The uniform threshold precedes every growing parameter and learner.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
--   - encoding: the transcript contains all queries, answers, and the final output, with at most D queries → a length-D table of optional query-answer pairs, padded by none after stopping, together with the final output; reason: under MakesAtMost D the representation retains every actual observation, including repeated queries and early stopping
--   - encoding: R(C_t) = Ω(t³), with Eq. (16) and the budget t³/10 in its proof → an absolute eventual exponent threshold, R_t > t³/10, the full Eq. (16) estimate, and for every integer D ≤ t³/10 the bounds 1/200, (e/5)^t and strict success <2/3; reason: retains the source proof’s explicit budget and errors; integer D automatically gives the floor convention
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 3.7, p.21, proof pp.27–28; Eq. (16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Experiments

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Theorem 3.7, p.21 and pp.27–28: full randomized minimum lower bound, Eq.(16), absolute budget 1/10, collision 1/200, exponential remainder, and strict distributional error threshold. No parameter lower bound is assumed. -/
theorem theorem_3_7 :
    (∀ (m : Size) (D : ℕ) (A : Learner m), A.MakesAtMost D →
      realSuccess m D A ≤
        (D + 1 : ℕ) / (t m : ℝ) ^ 6 + collisionError m D + epsilon m D) ∧
    (∃ m₀ : ℕ, ∀ m : Size, m₀ ≤ m.val →
      (t m : ℝ) ^ 3 / 10 < (R m : ℝ) ∧
      ∀ (D : ℕ) (A : Learner m), A.MakesAtMost D → (D : ℝ) ≤ (t m : ℝ) ^ 3 / 10 →
        collisionError m D ≤ 1 / 200 ∧
        epsilon m D ≤ (Real.exp 1 / 5) ^ t m ∧
        realSuccess m D A < 2 / 3) := by sorry

end ExactLearningSeparation678.Randomized
