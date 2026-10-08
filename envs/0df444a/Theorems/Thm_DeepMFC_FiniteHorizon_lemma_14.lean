-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_lemma_14
-- name    : DeepMFC.FiniteHorizon.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:01.434982+00:00
-- url     : https://prove2.me/theorems/15f21f9e-c2e7-4c19-bcc4-669b1837c6d5
-- title:
--   Lemma 14, p. 4078 — strong error of the Euler scheme: Σᵢ 𝔼|X̌ⁱ_{t_n} − Xⁱ_{t_n}|² ≤ CNΔt
-- statement:
--   Assume (A1)–(A4), (B1), (B3), (C1). For all $L,M\ge0$ there is a constant $C$ with the following property. Let $N,N_T\ge1$, $\Delta t=T/N_T$, $t_n=n\Delta t$, and let $\varphi$ be a feedback that is $L$-Lipschitz in $(t,x)$ on $[0,T]\times\mathbb R^d$ with $|\varphi(0,0)|\le M$. Let $(X^i)_{i\le N}$ solve the $N$-agent system (3.2) controlled by $\varphi$, and let $(\check X^i_{t_n})$ be the Euler scheme (2.13) with the same feedback, started at $\check X^i_0=X^i_0$ and driven by the Brownian increments $\Delta\check W^i_n=W^i_{t_{n+1}}-W^i_{t_n}$. Then for all $n=0,\dots,N_T$,
--   $$\sum_{i=1}^N\mathbb E\big[|\check X^i_{t_n}-X^i_{t_n}|^2\big]\le CN\Delta t.$$
--
--   This strong error estimate, with a constant independent of $N$, is what allows the comparison of the continuous-time and discrete-time $N$-agent costs.
--
--   **Formalization Note.** The coupling of the scheme with the continuous system (common initial positions and Brownian increments) is the one fixed on p. 4095 for the proof; the scheme is the deterministic map of Problem 2 evaluated at $(X^i_0(\omega),\Delta W^i_n(\omega))$. The expectation is a lower Lebesgue integral in $[0,\infty]$. $C$ depends on the data, the Lipschitz constant of $\varphi$ and a bound for $|\varphi(0,0)|$; it is uniform in $N$, $N_T$ and $n$. The lemma is stated under the standing assumption (A1), as the paper does (Remark 20).
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4078, Lemma 14; setting p. 4077; coupling p. 4095

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem lemma_14 {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D) :
    ∀ L Mφ : ℝ, ∃ C : ℝ, ∀ N NT : ℕ, 1 ≤ N → 1 ≤ NT →
      ∀ φ : ℝ → E d → Fin k → ℝ, FeedbackLip M L φ → ‖φ 0 0‖ ≤ Mφ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : Fin N → ℝ≥0 → Ω → E d)
        (X0 : Fin N → Ω → E d), Setting3 M P W X0 →
      ∀ X : Fin N → ℝ≥0 → Ω → E d, Solves32 M P W X0 φ X →
      ∀ n : ℕ, n ≤ NT →
        ∑ i, ∫⁻ ω, ‖euler M NT φ (fun j => X0 j ω)
              (fun j m => W j (M.tg NT ((m : ℕ) + 1)) ω - W j (M.tg NT m) ω) n i
            - X i (M.tg NT n) ω‖ₑ ^ 2 ∂P
          ≤ ENNReal.ofReal (C * N * ((M.T : ℝ) / NT)) := by sorry

end DeepMFC.FiniteHorizon
