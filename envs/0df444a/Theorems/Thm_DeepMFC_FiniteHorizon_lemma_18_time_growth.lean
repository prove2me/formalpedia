-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_lemma_18_time_growth
-- name    : DeepMFC.FiniteHorizon.lemma_18_time_growth
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T21:36:47.218587+00:00
-- url     : https://prove2.me/theorems/9ef55f6e-47ab-4b21-ab85-d3aff4040316
-- title:
--   Lemma 18 (corrected), p. 4089 — α̂ is Lipschitz in (x, μ, y) and (1+|y|)-Lipschitz in t
-- statement:
--   Assume (A1)–(A4), (B1), (B3), (C1), and let $\hat\alpha(t,x,\mu,y)$ minimize the reduced Hamiltonian $\alpha\mapsto\tilde H(t,x,\mu,y,\alpha)=b(t,x,\mu,\alpha)\cdot y+f(t,x,\mu,\alpha)$ over $\mathbb R^k$ for every $t\in[0,T]$, $x,y\in\mathbb R^d$ and $\mu\in\mathcal P_2(\mathbb R^d)$. Then there is a constant $L$, depending only on the data, such that for all $t,t'\in[0,T]$, $x,x',y,y'\in\mathbb R^d$ and $\mu,\mu'\in\mathcal P_2(\mathbb R^d)$,
--   $$|\hat\alpha(t,x,\mu,y)-\hat\alpha(t',x',\mu',y')|\le L\big((1+|y'|)\,|t-t'|+|x-x'|+W_2(\mu,\mu')+|y-y'|\big).$$
--
--   So $\hat\alpha$ is Lipschitz in $(x,\mu,y)$ uniformly in $t$, and Lipschitz in $t$ with a constant that grows linearly in $|y|$.
--
--   **Relation to the source.** This is Lemma 18 of the source with the time term corrected. The source states a plain Lipschitz bound $L(|t-t'|+\dots)$, but that bound fails when the coefficient $b_2(t)$ in (A1) depends on time. For $b=t\,\alpha$ and $f=\alpha^2$ one gets $\hat\alpha=-ty/2$, whose time increments grow with $|y|$; see the accepted disproof of `DeepMFC.FiniteHorizon.lemma_18`. The rest of Appendix A is unchanged. Only the term $(b_2(t)-b_2(t'))^{\top}y'$ needs the extra factor $|y'|$. Along the optimal feedback $y=V(t,x)$, which grows linearly in $x$, the bound still gives the Lipschitz control on bounded sets of $x$ that the later approximation steps use.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4089, Appendix A, Lemma 18 (time term corrected)

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem lemma_18_time_growth {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) (hmin : IsMinimizer M αhat) :
    ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ t' ∈ Set.Icc (0 : ℝ) M.T,
      ∀ (x x' : E d) (μ μ' : Measure (E d)) (y y' : E d), IsP2 μ → IsP2 μ' →
        ‖αhat t x μ y - αhat t' x' μ' y'‖
          ≤ L * ((1 + ‖y'‖) * |t - t'| + ‖x - x'‖ + (W2 μ μ').toReal + ‖y - y'‖) := by sorry

end DeepMFC.FiniteHorizon
