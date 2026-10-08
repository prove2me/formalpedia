-- Prove2me | Theorems.Thm_CondatPD_FB_lemma_4_1
-- name    : CondatPD.FB.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:39:53.471021+00:00
-- url     : https://prove2.me/theorems/459921a1-d141-46bf-bc12-094aebfc2a9d
-- title:
--   Lemma 4.1 — inexact Krasnosel'skii–Mann iteration
-- statement:
--   Let $T$ be a nonexpansive map on a real Hilbert space with a fixed point. For $0<\rho_n<1$, suppose the weighted errors are summable and the relaxation weights have divergent total mass:
--   $$\sum_{n\ge0}\rho_n\|e_n\|<\infty,\qquad\sum_{n\ge0}\rho_n(1-\rho_n)=+\infty.$$
--   Starting from any point, define $s_{n+1}=s_n+\rho_n(Ts_n+e_n-s_n)$. Then $s_n$ converges weakly to a fixed point of $T$.
--
--   This iteration lemma is the convergence step used by the forward–backward result.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 8, Lemma 4.1 and (13)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open Filter Topology

namespace CondatPD.FB

/-- Lemma 4.1, p. 8: Krasnosel'skii–Mann iteration with weighted errors. -/
theorem lemma_4_1 {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (T : K → K) (ρ : ℕ → ℝ) (e s : ℕ → K)
    (hT : ThreeOpSplitting.Convergence.IsNonexpansive T)
    (hfix : ∃ sh : K, T sh = sh)
    (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1)
    (hdiv : Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n * (1 - ρ n)) atTop atTop)
    (herr : Summable (fun n => ρ n * ‖e n‖))
    (hrun : ∀ n, s (n + 1) = s n + ρ n • (T (s n) + e n - s n)) :
    ∃ sh : K, T sh = sh ∧ ThreeOpSplitting.Convergence.WeakTendsto s sh := by sorry

end CondatPD.FB
