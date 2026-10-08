-- Prove2me | Theorems.Thm_ClosedLoopMFG_Limit_proposition_5_6
-- name    : ClosedLoopMFG.Limit.proposition_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:59.12599+00:00
-- url     : https://prove2.me/theorems/d67541d8-1db9-4bb1-b07d-de0dc95cca76
-- title:
--   Proposition 5.6 — a continuous semi-Markov deviation is the limit of unilateral $n$-player deviations (5.14)
-- statement:
--   Work in the setting of §5.5 (as in Lemma 5.5). Let $\beta\in\mathcal A^c_{\rm semi}$ be a continuous $A$-valued semi-Markov function, and for each $n$ and $k=1,\dots,n$ define the admissible $n$-player control
--   $$\beta^{n,k}(t,x)=\beta\Big(t,x^k_t,\frac1n\sum_{j=1}^n\delta_{x^j}\Big),\qquad t\in[0,T],\ x=(x^1,\dots,x^n)\in(\mathcal C^d)^n. \tag{5.13}$$
--   Then, along the subsequence of §5.5,
--   $$\lim_n\frac1n\sum_{k=1}^nJ^n_k\big(\alpha^{n,1},\dots,\alpha^{n,k-1},\beta^{n,k},\alpha^{n,k+1},\dots,\alpha^{n,n}\big)=J(\beta). \tag{5.14}$$
--
--   Combined with (5.8) and the $\varepsilon_n$-Nash property, this gives the optimality condition of the limiting weak RMFE.
--
--   **Formalization Note** The empirical measure $\frac1n\sum_j\delta_{x^j}$ in (5.13) acts through its flow $t\mapsto\frac1n\sum_j\delta_{x^j_t}\in C([0,T];\mathcal P(\mathbb R^d))$. The limit is along $n=\varphi(k)+1$ players, the subsequence of the §5.5 context; for each $k$ and each deviating player $j$ a weak solution of the deviated $(\varphi(k)+1)$-player system is given, and $J(\beta)$ is the reward of any solution of (5.10) with $\Lambda=\delta_\beta$ in the sense of Remark 2.6.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 31, Proposition 5.6, (5.13)–(5.14) (context: §5.5, p. 30)

import Mathlib
import Definitions.Def_ClosedLoopMFG_Limit_Model
import Definitions.Def_ClosedLoopMFG_Limit_Game
import Definitions.Def_ClosedLoopMFG_Limit_Equilibrium
import Definitions.Def_ClosedLoopMFG_Limit_Relaxed

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Limit

/-- **Proposition 5.6** (p. 31), in the standing context of §5.5. For a continuous `A`-valued
semi-Markov `β` and the `n`-player controls `β^{n,k}(t, x) = β(t, x^k_t, (1/n) ∑_j δ_{x^j})` of
(5.13), the average over `k` of player `k`'s payoff when `k` alone deviates to `β^{n,k}` converges,
along the subsequence of §5.5, to `J(β)` (5.14). -/
theorem proposition_5_6 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type} [NormedAddCommGroup EA]
    [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA] (A : Set EA) (lam : PR d)
    (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (hA : AssumptionA T A b f g)
    (α : (n : ℕ) → Fin (n + 1) → ℝ → (Fin (n + 1) → Path d T) → EA)
    (hα : ∀ n i, IsAdmissible A (α n i))
    (S : (n : ℕ) → NSol (n + 1) d T lam (drift b (α n))) (φ : ℕ → ℕ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → E d) (X : Ω → Path d T)
    (μ : Ω → Flow d T) (Λstar : ℝ → E d → Flow d T → PA A)
    (hctx : IsSec55Context lam b f g α S φ P W X μ Λstar)
    (β : ℝ → E d → Flow d T → EA) (hβ : IsContSemiMarkovCtrl A β)
    (S' : (k : ℕ) → (j : Fin (φ k + 1)) →
      NSol (φ k + 1) d T lam (drift b (Function.update (α (φ k)) j (betaNK β j))))
    (Xβ : Ω → Path d T) (hXβ : IsGenSol P W (fun ω => ev (X ω) 0) μ (strictDrift b β) Xβ) :
    Tendsto (fun k => (1 / ((φ k : ℝ) + 1)) *
        ∑ j : Fin (φ k + 1), (S' k j).J f g (Function.update (α (φ k)) j (betaNK β j)) j)
      atTop (𝓝 (reward P Xβ μ (strictRun f β) g)) := by sorry

end ClosedLoopMFG.Limit
