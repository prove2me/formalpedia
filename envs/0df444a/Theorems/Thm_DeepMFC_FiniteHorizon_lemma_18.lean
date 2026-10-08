-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_lemma_18
-- name    : DeepMFC.FiniteHorizon.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:49.445855+00:00
-- url     : https://prove2.me/theorems/0c45a68c-3cb1-40e3-b524-0394159d1934
-- title:
--   Lemma 18, p. 4089 — the minimizer α̂(t, x, μ, y) of the reduced Hamiltonian is Lipschitz in all its variables
-- statement:
--   Assume (A1)–(A4), (B1), (B3), (C1), and let $\hat\alpha(t,x,\mu,y)$ minimize the reduced Hamiltonian $\alpha\mapsto\tilde H(t,x,\mu,y,\alpha)=b(t,x,\mu,\alpha)\cdot y+f(t,x,\mu,\alpha)$ over $\mathbb R^k$ for every $t\in[0,T]$, $x,y\in\mathbb R^d$ and $\mu\in\mathcal P_2(\mathbb R^d)$. Then there is a constant $L$ such that for all $t,t'\in[0,T]$, $x,x',y,y'\in\mathbb R^d$ and $\mu,\mu'\in\mathcal P_2(\mathbb R^d)$,
--   $$|\hat\alpha(t,x,\mu,y)-\hat\alpha(t',x',\mu',y')|\le L\big(|t-t'|+|x-x'|+W_2(\mu,\mu')+|y-y'|\big).$$
--
--   The Lipschitz continuity of the minimizer is what makes the optimal feedback $\hat v$ Lipschitz, which every later approximation step needs.
--
--   **Formalization Note.** The constant depends only on the data (through the hypotheses), as on the page. Section 2.2 lists the Lipschitz property among the standing assumptions, but Appendix A proves it from (A1)–(A4) and (B1); it is therefore a theorem here, not a hypothesis.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4089, Appendix A, Lemma 18

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem lemma_18 {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) (hmin : IsMinimizer M αhat) :
    ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ t' ∈ Set.Icc (0 : ℝ) M.T,
      ∀ (x x' : E d) (μ μ' : Measure (E d)) (y y' : E d), IsP2 μ → IsP2 μ' →
        ‖αhat t x μ y - αhat t' x' μ' y'‖
          ≤ L * (|t - t'| + ‖x - x'‖ + (W2 μ μ').toReal + ‖y - y'‖) := by sorry

end DeepMFC.FiniteHorizon
