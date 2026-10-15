-- Prove2me | Theorems.Thm_BreakingSample_Perturbed_lemma_6
-- name    : BreakingSample.Perturbed.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:09.392775+00:00
-- url     : https://prove2.me/theorems/14c0c81b-d5b3-412f-8371-bcd64c258119
-- title:
--   Lemma 6 — uniform reward perturbations separate optimal Q values
-- statement:
--   Add independent $\operatorname{Unif}(0,\xi)$ perturbations $\zeta(s,a)$ to every reward, where $\xi>0$. For a fixed transition kernel and $\delta>0$, with probability at least $1-\delta$ over $\zeta$, every optimal policy of the perturbed MDP has, at every state, a strict action-value gap over all other actions:
--
--   $$Q_p^\star(s,\pi_p^\star(s))-Q_p^\star(s,a)>\frac{\xi\delta(1-\gamma)}{3|S||A|^2}\quad(a\ne\pi_p^\star(s)).$$
--
--   The same statement applies to the empirical transition kernel after it is fixed, giving the separation used for perturbed empirical planning.
--
--   **Formalization Note** A finite nonempty state set is assumed. The failure event is bounded in extended nonnegative measure, avoiding a default real value for a nonmeasurable section.
-- source:
--   arXiv:2005.12900v8, Lemma 6, (45)–(46), p. 17

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling

namespace BreakingSample.Perturbed

open MeasureTheory

/-- Lemma 6 and (46), arXiv:2005.12900v8, p. 17, for any fixed kernel. -/
theorem lemma_6 {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ ξ δ : ℝ)
    (hM : IsDiscountedMDP P r γ) (hξ : 0 < ξ) (hδ : 0 < δ) :
    unifCube S A ξ {ζ | ¬ ∀ π : S → A,
      IsOptimal P (fun s a => r s a + ζ s a) γ π →
      ∀ s a, a ≠ π s →
        optQ P (fun s a => r s a + ζ s a) γ s a +
          ξ * δ * (1 - γ) / (3 * Fintype.card S * (Fintype.card A : ℝ) ^ 2) <
        optQ P (fun s a => r s a + ζ s a) γ s (π s)} ≤
      ENNReal.ofReal δ := by sorry

end BreakingSample.Perturbed
