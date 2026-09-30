-- Prove2me | Theorems.Thm_AlgMechDesign_Rounding_rounding_mechanism_truthful_approx
-- name    : AlgMechDesign.Rounding.rounding_mechanism_truthful_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:29:37.467611+00:00
-- url     : https://prove2.me/theorems/a5b4a2c7-6002-46be-aafd-7065e44cbd98
-- title:
--   Theorem 5.9 — the rounding mechanism is truthful and yields a $(1+\varepsilon)$-approximation
-- statement:
--   Let $0 < a < b$ bound the task times, let $\varepsilon > 0$, let $0 < \delta \le \varepsilon a$ be the rounding step, and let $x(\cdot)$ be any allocation algorithm that, on declarations in $[a,b]$, exactly solves the problem with declarations rounded up to multiples of $\delta$ (ties arbitrary). Consider the rounding mechanism with verification: allocation $x(d)$, payment $p^i = c^i + b^i$ with compensation $c^i = \sum_{j\in x^i(d)} \tilde t_j$ and bonus $b^i = -\hat g(x(d), \mathrm{corr}^i(x(d), d, \tilde t))$. Then:
--
--   1. **Truthfulness.** For every agent $i$ and true type $t^i \in [a,b]^k$ some strategy declaring $t^i$ is dominant.
--   2. **Approximation.** For every true type vector $t \in [a,b]^{n\times k}$ and every strategy profile in which each agent's strategy is dominant for its true type and belongs to the class named in the proof (declaration with the same rounded value as the true type; executions whose rounded times equal the rounded true times), the outcome $x = x(d)$ with actual times $\tilde t$ satisfies
--   $$g(x,\tilde t) \le (1+\varepsilon)\, g(y,t) \quad\text{for every allocation } y.$$
--
--   This is Theorem 5.9 of Nisan and Ronen with the running-time claim removed: an approximation algorithm, rather than an exact optimizer, can be made truthful once the mechanism can verify execution times.
--
--   **Formalization Note** "Polynomial time" is not formalized; the Horowitz–Sahni algorithm enters only through its specification (it solves the rounded problem exactly), which is how Definition 34 uses it. The statement is for every $\delta \in (0,\varepsilon a]$, covering the intended $\delta = \varepsilon a$; $b$ is kept as part of the bounded problem but plays no role once running time is dropped. Definition 3 asks for the specification at *every* profile of dominant strategies; part 2 restricts to dominant profiles of the class the paper's proof claims to be the only dominant strategies. The restriction is necessary: with $n=2$, $k=1$, $a=1$, $b=2$, $\varepsilon=\delta=1/4$, true times $(1.01, 1.5)$ and the allocation that gives the task to agent $1$ unless agent $2$'s rounded declaration is strictly smaller, the declarations $(1.5, 1.25)$ with minimal execution are both dominant, yet the task goes to agent $2$ and the make-span $1.5$ exceeds $(1+\varepsilon)\cdot 1.01$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 193, Theorem 5.9 and its proof (sketch); p. 172, Definition 3; p. 186, Definition 19; p. 193, Definition 34

import Mathlib
import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism

namespace AlgMechDesign.Rounding

/-- Theorem 5.9 (p. 193), without running time: for every fixed `ε > 0`, every rounding step
`0 < δ ≤ ε a` and every allocation algorithm that exactly solves the rounded problem (ties
arbitrary), the rounding mechanism with verification for the bounded task scheduling problem
(times in `[a, b]`, `0 < a < b`) is truthful, and whenever every agent plays a strategy of the
class the proof names (declare a type with the same rounded value as the true type, execute so that
rounded actual times equal rounded true times), the outcome's make-span with actual times is at
most `1 + ε` times the optimal make-span for the true types. -/
theorem rounding_mechanism_truthful_approx {n k : ℕ} [NeZero n] (a b ε δ : ℝ) (ha : 0 < a)
    (hab : a < b) (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε * a)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (halloc : IsRoundedOptimal a b δ alloc) :
    Truthful a b alloc (roundingPay δ alloc) ∧
    ∀ t : Fin n → Fin k → ℝ, IsBoundedType a b t →
      ∀ (D : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k),
        (∀ l : Fin n, Dominant a b alloc (roundingPay δ alloc) l (t l) (D l) (E l)) →
        (∀ l : Fin n, RoundsLikeTruth δ l (t l) (D l) (E l)) →
          ∀ y : Fin k → Fin n,
            gT (alloc D) (actualTimes alloc D E) ≤ (1 + ε) * makespan t y := by sorry

end AlgMechDesign.Rounding
