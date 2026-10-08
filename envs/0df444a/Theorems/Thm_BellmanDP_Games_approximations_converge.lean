-- Prove2me | Theorems.Thm_BellmanDP_Games_approximations_converge
-- name    : BellmanDP.Games.approximations_converge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T21:16:40.75795+00:00
-- url     : https://prove2.me/theorems/78f95698-53b6-4b0e-8966-cdc336fc3d28
-- title:
--   Chapter X, Theorem 3 — successive approximations from any admissible $f_0$ converge
-- statement:
--   Under the assumptions of Theorem 1 of Chapter X, let $f_0(P,P')$ be any function that is continuous for $P\in D$, $P'\in D'$ and equal to zero at $P=0$, $P'=0$. Then the sequence
--   $$f_{N+1}(P,P')=\max_G\min_{G'}T(P,P';f_N;G,G')=\min_{G'}\max_G T(P,P';f_N;G,G'),\qquad N=0,1,\dots$$
--   is well defined, and it converges to the solution $f$ of the equation (the solution in the class of Theorem 1), uniformly in every bounded region $\|P\|+\|P'\|\le c$.
--
--   The theorem justifies approximation in strategy space: the iteration may be started from any admissible guess, not only from the one-stage value.
--
--   **Formalization Note** Bellman writes only "converges". The mode stated here, uniform convergence on bounded regions, is the mode of Theorem 1, whose proof Bellman says is "precisely the same"; it implies pointwise convergence. "The solution" is any solution in Theorem 1's class, which Theorem 1 shows is unique.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter X, § 15, Theorem 3, p. 300

import Mathlib
import Definitions.Def_BellmanDP_Games_MultiStage

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, Theorem 3, p. 300. Under the assumptions of Theorem 1
(`GameHyp g k`), for any initial function `f₀` continuous on `D × D'` with `f₀(0, 0) = 0`, the
sequence `f_{N+1}(P, P') = Max_G Min_{G'} T(P, P'; f_N; G, G') = Min_{G'} Max_G T(P, P'; f_N; G, G')`
is defined, and it converges to the solution `f` of (12.3) (the solution in the class of
Theorem 1), uniformly in every bounded region of `(P, P')` space. -/
theorem approximations_converge {n n' m m' : ℕ} (g : GameData n n' m m') (k : ℝ)
    (hg : GameHyp g k) (f₀ : Vec n → Vec n' → ℝ) (hf₀ : InSolutionClass g f₀) :
    (∃ fs : ℕ → Vec n → Vec n' → ℝ, fs 0 = f₀ ∧ IsIterSeq g fs) ∧
      ∀ f : Vec n → Vec n' → ℝ, InSolutionClass g f → IsGameSolution g f →
      ∀ fs : ℕ → Vec n → Vec n' → ℝ, fs 0 = f₀ → IsIterSeq g fs →
        ∀ c : ℝ, TendstoUniformlyOn (fun N (z : Vec n × Vec n') => fs N z.1 z.2)
          (fun z => f z.1 z.2) Filter.atTop (region g c) := by sorry

end BellmanDP.Games
