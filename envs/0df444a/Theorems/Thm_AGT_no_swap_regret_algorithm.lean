-- Prove2me | Theorems.Thm_AGT_no_swap_regret_algorithm
-- name    : AGT.no_swap_regret_algorithm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T03:33:55.903968+00:00
-- url     : https://prove2.me/theorems/5f3c7754-8f07-4cfc-a9ae-5fc2d7cc0dcd
-- title:
--   An online algorithm with vanishing swap regret
-- statement:
--   There is an online algorithm whose swap regret against every adversary is at most $2N\sqrt{T\ln N}$ — the mission goal, Corollary 4.16 of *Algorithmic Game Theory* in explicit form. For every number of actions $N = n+1$ and every known horizon $T$ there exists an online algorithm $H$, playing a genuine probability distribution after every history, whose swap regret is uniformly small: against every $[0,1]$-valued loss sequence and every modification rule $F$,
--   $$L^T_H \;\le\; L^T_{H,F} + 2N\sqrt{T\,\ln N}.$$
--   Per round, the swap regret vanishes at rate $2N\sqrt{\ln N/T}$; combined with Theorem 4.12, if every player of a finite game runs such an algorithm, the empirical joint play is a $2N\sqrt{\ln N/T}$-correlated equilibrium — the chapter's punchline, and the algorithmic foundation of correlated equilibrium.
--
--   *A note on the constant and the quantifiers.* The book states the bound as $O(N\sqrt{T\log N})$; the constant $2$ is the one its own route produces — Polynomial Weights tuned at $\eta = \min\{\sqrt{\ln N/T}, 1/2\}$ has external regret $\le 2\sqrt{T\ln N}$ (in the small-horizon regime $T < 4\ln N$ this follows from the trivial bound $L \le T \le 2\sqrt{T\ln N}$ rather than from the potential argument), and the reduction of Theorem 4.15 multiplies it by $N$. The algorithm is quantified before the loss sequence and the rule $F$: one $H$ must serve every adversary, so no witness can be chosen with hindsight. $H$ may depend on $T$ (the book's known-horizon convention; guess-and-double removes this at a constant-factor cost and is out of scope).
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 4.5, Corollary 4.16, p. 94 (explicit constant)

import Definitions.Def_agt_regret
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace AGT

/-- **Corollary 4.16 of *Algorithmic Game Theory* (explicit form)**, the
capstone of Chapter 4: there is an online algorithm with vanishing swap
regret.  For every number of actions `n + 1` and every known horizon `T`
there is an online algorithm `H` playing genuine distributions such that
against every `[0,1]`-valued loss sequence and every modification rule `F`,
`L_H ≤ L_{H,F} + 2 (n+1) √(T ln(n+1))`.

The explicit constant is the one the chapter's own route produces: the
Polynomial Weights bound (Theorem 4.6) tuned at `η = min{√(ln N / T), 1/2}`
gives external regret `2√(T ln N)`, and the external-to-swap reduction
(Theorem 4.15) multiplies it by `N`.  Combined with Theorem 4.12, an `H` of
this quality for every player drives the empirical joint play into an
`ε`-correlated equilibrium at rate `ε = 2N√(ln N / T)`. -/
theorem no_swap_regret_algorithm {n : ℕ} (T : ℕ) :
    ∃ H : OnlineAlgorithm (n + 1), (∀ h, IsLottery (H h)) ∧
      ∀ ℓ : ℕ → Fin (n + 1) → ℝ, (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
        ∀ F : Fin (n + 1) → Fin (n + 1),
          algLoss H ℓ T ≤ swapLoss H ℓ F T +
            2 * (n + 1) * Real.sqrt (T * Real.log (n + 1)) := by
  sorry

end AGT
