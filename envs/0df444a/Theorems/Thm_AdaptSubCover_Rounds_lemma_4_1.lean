-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_lemma_4_1
-- name    : AdaptSubCover.Rounds.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:41.378335+00:00
-- url     : https://prove2.me/theorems/eb62d9d9-f2da-4671-a969-d326b08437d9
-- title:
--   Lemma 4.1, p. 11 — NA terminates by time t iff the time-t prefix is realized in a scale θ ≤ δ (or covers f), for non-integral τ
-- statement:
--   Let $f$ be monotone submodular with $Q > 0$, let $\delta = 2^{-z}$, $\tau = Q(1-\delta)$, and let $L$ be ParCA's greedy list. Let $t \ge 0$ be smaller than the total cost of $L$ (so that the item $\mathcal X_{e(t)}$ exists), and let $\mathcal S$ be the set of items chosen until time $t$, with realization $S$. If $\tau$ is not an integer, then
--
--   $$\mathtt{NA}\text{ terminates by time } t \iff S \in \mathcal E_\theta \text{ for some scale } \theta \le \delta, \text{ or } f(S) = Q.$$
--
--   This lemma ties the termination of the non-adaptive strategy to the scale structure of the realizations; it is used to rewrite (5) and in (12).
--
--   **Formalization Note.** As printed, the equivalence fails in two corner cases, which the hypotheses repair: if $f(S) = \tau$ (possible only when $\tau$ is an integer) the realization is in scale $\delta$ but $\mathtt{NA}$, which stops only when $f > \tau$, has not terminated; and if $f(S) = Q$ the realization lies in no scale, since $(Q - f(S))/Q = 0$, although $\mathtt{NA}$ has terminated — hence the extra disjunct. The two implications displayed in the paper's proof hold without these repairs. "Terminates by time $t$" means $\mathtt{NA}$ never probes $\mathcal X_{e(t)}$; $\theta \le \delta$ is $j \ge z$.
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 11, Lemma 4.1

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis

namespace AdaptSubCover.Rounds

theorem lemma_4_1 {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (z : ℕ) (hτ : ∀ n : ℕ, (n : ℝ) ≠ I.tau z)
    (L : List (Fin m)) (hL : I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t < (I.cumCost L L.length : ℝ)) (ω : Fin m → U) :
    I.NAStoppedBy (I.tau z) L t ω ↔
      ((∃ j : ℕ, z ≤ j ∧ I.InScale j (I.prefixAt L t) ω) ∨
        I.f ((I.prefixAt L t).image ω) = I.Q) := by sorry

end AdaptSubCover.Rounds
