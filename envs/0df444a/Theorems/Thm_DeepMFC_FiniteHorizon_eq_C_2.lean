-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_eq_C_2
-- name    : DeepMFC.FiniteHorizon.eq_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:51.521632+00:00
-- url     : https://prove2.me/theorems/3482b348-28af-4552-840e-6c36c4230326
-- title:
--   (C.2), p. 4092 — 𝔼 sup_{t≤T} |X^{i,φ}_t|² ≤ C and 𝔼 sup_{t≤T} |X^{i,φ}_t|⁴ ≤ C for Lipschitz feedbacks, uniformly in N
-- statement:
--   Assume (A1)–(A4), (B1), (B3), (C1). For all $L,M\ge0$ there is a constant $C$ such that for every $N\ge1$, every feedback $\varphi$ that is $L$-Lipschitz in $(t,x)$ on $[0,T]\times\mathbb R^d$ with $|\varphi(0,0)|\le M$, every solution $(X^{i,\varphi})_{i=1,\dots,N}$ of the $N$-agent system (3.2) controlled by $\varphi$, and every $i$,
--   $$\mathbb E\Big[\sup_{t\in[0,T]}|X^{i,\varphi}_t|^2\Big]\le C,\qquad\mathbb E\Big[\sup_{t\in[0,T]}|X^{i,\varphi}_t|^4\Big]\le C.$$
--
--   These moment bounds, uniform in the number of agents, are the stability estimate behind the exit-probability bound in the proof of Proposition 13.
--
--   **Formalization Note.** The expectations of the suprema are lower Lebesgue integrals in $[0,\infty]$. The constant depends on the data, on the Lipschitz constant of the feedback and on a bound for $|\varphi(0,0)|$ (the proof lists $v(0,0)$, $w(0,0)$ among its dependencies, p. 4092); it is uniform in $N$ and $i$.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4092, Appendix C, proof of Proposition 13, (C.2)

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem eq_C_2 {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D) :
    ∀ L Mφ : ℝ, ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∀ φ : ℝ → E d → Fin k → ℝ, FeedbackLip M L φ → ‖φ 0 0‖ ≤ Mφ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : Fin N → ℝ≥0 → Ω → E d)
        (X0 : Fin N → Ω → E d), Setting3 M P W X0 →
      ∀ X : Fin N → ℝ≥0 → Ω → E d, Solves32 M P W X0 φ X →
      ∀ i : Fin N,
        ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : t ≤ M.T), ‖X i t ω‖ₑ) ^ 2 ∂P ≤ ENNReal.ofReal C ∧
        ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : t ≤ M.T), ‖X i t ω‖ₑ) ^ 4 ∂P ≤ ENNReal.ofReal C := by sorry

end DeepMFC.FiniteHorizon
