-- Prove2me | Theorems.Thm_CondatPD_FB_lemma_4_4
-- name    : CondatPD.FB.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:39:46.766759+00:00
-- url     : https://prove2.me/theorems/f5dd16e6-944f-4c98-881f-ca0383740acc
-- title:
--   Lemma 4.4 — inexact relaxed forward–backward iteration
-- statement:
--   Let $M_1$ be maximally monotone and $M_2$ be $\kappa$-cocoercive on a real Hilbert space, with $\kappa>0$ and a nonempty zero set of $M_1+M_2$. Let $0<\gamma\le2\kappa$ and $\delta=2-\gamma/(2\kappa)$. If $0<\rho_n<\delta$, $\sum_n\rho_n(\delta-\rho_n)=+\infty$, and both weighted error norms $\sum_n\rho_n\|e_{1,n}\|$ and $\sum_n\rho_n\|e_{2,n}\|$ are finite, then the iteration
--   $$s_{n+1}=\rho_n\bigl((I+\gamma M_1)^{-1}(s_n-\gamma(M_2s_n+e_{2,n}))+e_{1,n}\bigr)+(1-\rho_n)s_n$$
--   converges weakly to a zero of $M_1+M_2$.
--
--   This is the abstract convergence result instantiated by both primal–dual algorithms.
--
--   **Formalization Note** A resolvent map is a parameter satisfying its defining inclusion. The published cocoercivity predicate is equivalent, for $\kappa>0$, to the paper's firm nonexpansiveness statement for $\kappa M_2$.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 9, Lemma 4.4, (17)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open Filter Topology

namespace CondatPD.FB

/-- Lemma 4.4, p. 9: inexact relaxed forward–backward iteration. -/
theorem lemma_4_4 {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (M₁ : K → Set K) (M₂ : K → K) (κ γ : ℝ)
    (ρ : ℕ → ℝ) (e₁ e₂ s : ℕ → K) (J : K → K)
    (hM₁ : ThreeOpSplitting.Convergence.IsMaximalMonotone M₁)
    (hκ : 0 < κ)
    (hM₂ : ThreeOpSplitting.Convergence.IsCocoercive κ M₂)
    (hzero : (ThreeOpSplitting.Convergence.zer
      (fun t : K => {w : K | ∃ a ∈ M₁ t, w = a + M₂ t})).Nonempty)
    (hγ : 0 < γ ∧ γ ≤ 2 * κ)
    (hρ : ∀ n, 0 < ρ n ∧ ρ n < 2 - γ / (2 * κ))
    (hdiv : Tendsto (fun N => ∑ n ∈ Finset.range N,
      ρ n * ((2 - γ / (2 * κ)) - ρ n)) atTop atTop)
    (he₁ : Summable (fun n => ρ n * ‖e₁ n‖))
    (he₂ : Summable (fun n => ρ n * ‖e₂ n‖))
    (hJ : ThreeOpSplitting.Convergence.IsResolvent γ M₁ J)
    (hrun : ∀ n, s (n + 1) =
      ρ n • (J (s n - γ • (M₂ (s n) + e₂ n)) + e₁ n) + (1 - ρ n) • s n) :
    ∃ sh : K, sh ∈ ThreeOpSplitting.Convergence.zer
      (fun t : K => {w : K | ∃ a ∈ M₁ t, w = a + M₂ t}) ∧
      ThreeOpSplitting.Convergence.WeakTendsto s sh := by sorry

end CondatPD.FB
