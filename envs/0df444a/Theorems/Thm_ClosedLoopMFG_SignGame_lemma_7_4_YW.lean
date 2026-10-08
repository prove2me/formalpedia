-- Prove2me | Theorems.Thm_ClosedLoopMFG_SignGame_lemma_7_4_YW
-- name    : ClosedLoopMFG.SignGame.lemma_7_4_YW
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:24:06.04399+00:00
-- url     : https://prove2.me/theorems/796f9df3-44f2-4691-811e-1f785c271cfc
-- title:
--   Lemma 7.4 (the (Y, W) part) — the laws of (μ̄^n, W^1) are tight and every limit has L(Y) = ½δ_{H⁺_0}+½δ_{H⁻_0}, Y_t = ∫sgn(Y_s)ds, Y ⫫ W
-- statement:
--   In the $n$-player mean-sign game with horizon $T>0$, let player 1 use a Markovian control $\beta^n:[0,T]\times\mathbb R^n\to[-1,1]$ that is $\tfrac1n$-optimal against the sign feedback of the others, as in (7.15):
--
--   $$
--   \sup_{\beta\in\mathcal{AM}_n}J^n_1(\beta,\alpha^{n,2}_0,\dots,\alpha^{n,n}_0)\ \le\ J^n_1(\beta^n,\alpha^{n,2}_0,\dots,\alpha^{n,n}_0)+\frac1n ,
--   $$
--
--   while players $2,\dots,n$ keep $\alpha^{n,k}_0$. On a solution of this profile let $Y^n=\overline\mu^n$ be the mean process and $W^1$ player 1's Brownian motion, both as $C([0,T];\mathbb R)$-valued random variables. Then:
--
--   1. the laws of $(Y^n,W^1)$ on $C([0,T];\mathbb R)^2$ form a tight family;
--   2. every weak limit $(Y,W)$ along a subsequence satisfies
--      - (i) $\mathcal L(Y)=\tfrac12\delta_{H^+_0}+\tfrac12\delta_{H^-_0}$, with $H^\pm_0(t)=\pm t$;
--      - (ii) almost surely, $Y_t=\int_0^t\operatorname{sgn}(Y_s)\,ds$ for all $t\in[0,T]$;
--      - (iv) $Y$ and $W$ are independent.
--
--   This is the compactness step of the proof of Proposition 7.2: passing to the limit in $J^n_1(\beta^n,\dots)=\mathbb E[X^n_TY^n_T]$ along such subsequences gives (7.14).
--
--   **Formalization Note** The paper's Lemma 7.4 concerns the quadruple $(X^n,Y^n,W^1,\beta^n)$ with $\beta^n$ in $L^2([0,T];[-1,1])$ under the weak topology of $L^2$; this statement keeps only the $(Y,W)$ coordinates, and so omits the equation for $X$ and item (iii) (the Brownian property of $W$ in the joint filtration). The $(Y,W)$ conclusions are unchanged by the omission. Hypothesis (7.15) is stated for every solution of every deviation and every solution under $\beta^n$; term $n$ of the sequence is the $(n+1)$-player game, so $\frac1n$ becomes $\frac1{n+1}$. Weak convergence of the laws is written through bounded continuous test functions, and the statement asserts that $(Y^n,W^1)$ is (almost everywhere) measurable, so its law is a probability measure. Independence is written as: the joint law equals the product of its marginals. Player 1 is index $0$.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 50, (7.15) and Lemma 7.4

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ClosedLoopMFG_SignGame_Model
import Definitions.Def_ClosedLoopMFG_SignGame_Game
import Definitions.Def_ClosedLoopMFG_SignGame_Example

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.SignGame

/-- Lemma 7.4 (the `(Y, W)` part), p. 50. Player 1 deviates to a Markovian control `β^n`
chosen as in (7.15); the others keep the sign feedback. The laws of `(Y^n, W^1)` (mean process,
player 1's Brownian motion) are tight on `C × C`, and every subsequential weak limit `(Y, W)`
satisfies (i) `L(Y) = ½δ_{H⁺_0} + ½δ_{H⁻_0}`, (ii) `Y_t = ∫_0^t sgn(Y_s) ds`, and (iv) `Y`, `W`
independent. Term `n` of the sequence is the `(n + 1)`-player game. -/
theorem lemma_7_4_YW (T : ℝ≥0) (hT : 0 < T)
    (β : (n : ℕ) → ℝ → (Fin (n + 1) → EthierKurtz.SDEState 1) → ℝ)
    (hβ : ∀ n, IsMarkovianControl T signA (β n))
    (h715 : ∀ n (β' : ℝ → (Fin (n + 1) → EthierKurtz.SDEState 1) → ℝ),
      IsMarkovianControl T signA β' →
      ∀ (S' : NSol (n + 1) 1 T signLam
          (signDrift T (Function.update (signProfile (n + 1) T) 0 β')))
        (S'' : NSol (n + 1) 1 T signLam
          (signDrift T (Function.update (signProfile (n + 1) T) 0 (β n)))),
        signPayoff S' 0 ≤ signPayoff S'' 0 + 1 / ((n : ℝ) + 1))
    (S : (n : ℕ) → NSol (n + 1) 1 T signLam
      (signDrift T (Function.update (signProfile (n + 1) T) 0 (β n)))) :
    (∀ n, AEMeasurable (ywMap (S n)) (S n).P) ∧
    IsTightMeasureSet (Set.range fun n => ywLaw (S n)) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ν : ProbabilityMeasure (RPath T × RPath T),
      (∀ h : BoundedContinuousFunction (RPath T × RPath T) ℝ,
        Tendsto (fun k => ∫ z, h z ∂ywLaw (S (φ k))) atTop
          (𝓝 (∫ z, h z ∂(ν : Measure (RPath T × RPath T))))) →
      (ν : Measure (RPath T × RPath T)).map Prod.fst = (halfMix T : Measure (RPath T)) ∧
      (∀ᵐ z ∂(ν : Measure (RPath T × RPath T)), ∀ t : Set.Icc (0 : ℝ) T,
        z.1 t = ∫ s in (0 : ℝ)..(t : ℝ), Real.sign (z.1 (ClosedLoopMFG.Limit.clampT T s))) ∧
      (ν : Measure (RPath T × RPath T)) =
        ((ν : Measure (RPath T × RPath T)).map Prod.fst).prod
          ((ν : Measure (RPath T × RPath T)).map Prod.snd) := by sorry

end ClosedLoopMFG.SignGame
