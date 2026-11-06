-- Prove2me | Theorems.Thm_DelayedGamesMAO_lemma_1
-- name    : DelayedGamesMAO.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:52.024196+00:00
-- url     : https://prove2.me/theorems/59732fa3-ad7e-46a8-90b4-d36c2b60575f
-- title:
--   Lemma 1 — delays-to-feedback decomposition (4)
-- statement:
--   Let $W$ be a nonempty compact convex subset of a finite-dimensional real normed space, $T\ge1$, and $(d_t)$ delays with $t+d_t\le T$. Let $g_1,\dots,g_T$ be gradients and $h_1,\dots,h_{T+1}$ hints (dual vectors) with $h_1=h_{T+1}=0$, and let $w_1,\dots,w_{T+1}\in W$. Then for every $u\in W$,
--   $$
--   \sum_{t=1}^T\langle g_t,w_t-u\rangle=\sum_{t=1}^T\Bigl\langle h_{t+1}+\sum_{s\in N_t}(g_s-h_s),\,w_{t+1}-u\Bigr\rangle+\sum_{t=1}^T\sum_{s\in N_t}\langle g_s-h_s,\,w_s-w_{t+1}\rangle .
--   $$
--
--   The right-hand side involves only quantities observable at the end of each round, which motivates the optimistic multi-anchor update.
--
--   Differences from the source:
--   - encoding: W ⊆ ℝⁿ with a norm ‖·‖ and dual norm ‖·‖∗; gradients and hints in ℝⁿ → a finite-dimensional real normed space E; gradients and hints are continuous linear functionals E →L[ℝ] ℝ with the operator norm; reason: ℝⁿ with any norm is such a space and every such space is ℝⁿ with a norm; the operator norm is the dual norm; same instances
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5, Lemma 1, eq. (4), p.8; proof p.15

import Mathlib
import Definitions.Def_DelayedGamesMAO_newObs

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Lemma 1 (delays-to-feedback decomposition).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5, Lemma 1, eq. (4), p.8 (proof p.15): "For any `u ∈ W` and any sequence
`h_1, …, h_{T+1} ∈ ℝⁿ` of hints with `h_1 = h_{T+1} = 0`,
`∑_{t=1}^T ⟨g_t, w_t − u⟩ = ∑_{t=1}^T ⟨h_{t+1} + ∑_{s∈N_t}(g_s − h_s), w_{t+1} − u⟩
+ ∑_{t=1}^T ∑_{s∈N_t} ⟨g_s − h_s, w_s − w_{t+1}⟩`."

`g t` is the gradient of round `t`, `w t ∈ W` the action of round `t` (`w_{T+1}` the
iterate after the last round), `h t` the hint of round `t`.

**Formalization Note.** `W` is the protocol's nonempty compact convex domain in a
finite-dimensional real normed space `E` (the paper's `ℝⁿ` with a norm); gradients and hints
are dual vectors `E →L[ℝ] ℝ`, and `⟨g, x⟩` is `g x`. The protocol's `t + d_t ≤ T` is a
hypothesis. -/
theorem lemma_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Set E) (hWne : W.Nonempty) (hWc : IsCompact W) (hWcv : Convex ℝ W)
    (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (g h : ℕ → E →L[ℝ] ℝ) (w : ℕ → E) (hw : ∀ t ∈ Finset.Icc 1 (T + 1), w t ∈ W)
    (hh1 : h 1 = 0) (hhT : h (T + 1) = 0) :
    ∀ u ∈ W, ∑ t ∈ Finset.Icc 1 T, g t (w t - u) =
      ∑ t ∈ Finset.Icc 1 T, (h (t + 1) + ∑ s ∈ newObs d t, (g s - h s)) (w (t + 1) - u) +
        ∑ t ∈ Finset.Icc 1 T, ∑ s ∈ newObs d t, (g s - h s) (w s - w (t + 1)) := by sorry

end DelayedGamesMAO
