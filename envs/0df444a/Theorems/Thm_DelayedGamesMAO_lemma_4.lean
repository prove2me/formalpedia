-- Prove2me | Theorems.Thm_DelayedGamesMAO_lemma_4
-- name    : DelayedGamesMAO.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:55.244273+00:00
-- url     : https://prove2.me/theorems/4aceb1f0-0445-4756-9df6-7a2f378a6cd8
-- title:
--   Lemma 4 — the hint-anchor penalty is at most $M\sigma_{\max}$
-- statement:
--   Let $W$ be a nonempty compact convex subset of a finite-dimensional real normed space and let $\psi$, $w_0$, $M$ satisfy Assumption 2. Let $T\ge1$, $(d_t)$ delays with $t+d_t\le T$, and $s_1,\dots,s_{T+1}$ satisfying the assumptions of Lemma 3. Let $(w_t)$ be a sequence with $w_0$ the reference point and $w_t\in W$ for $t\in[T]$. Then for every $u\in W$,
--   $$
--   \sum_{t=1}^T\bigl(D_\psi(u\mid w_{s_{t+1}})-D_\psi(u\mid w_t)\bigr)\le M\sigma_{\max}.
--   $$
--
--   This bounds the extra Bregman terms created by the additional anchor at the hint source, which produces the negative movement terms needed in games.
--
--   Differences from the source:
--   - encoding: W ⊆ ℝⁿ with a norm ‖·‖ and dual norm ‖·‖∗; gradients and hints in ℝⁿ → a finite-dimensional real normed space E; gradients and hints are continuous linear functionals E →L[ℝ] ℝ with the operator norm; reason: ℝⁿ with any norm is such a space and every such space is ℝⁿ with a norm; the operator norm is the dual norm; same instances
--   - generalization: ψ differentiable on W with gradient ∇ψ, and D_ψ(u | w) = ψ(u) − ψ(w) − ⟨∇ψ(w), u − w⟩ → a derivative field dψ of ψ within W (IsGradientOn) and D_ψ = TimeVaryingGames.bregman ψ dψ; reason: the gradient of a differentiable ψ is such a field, so the statement specializes to the paper's; it asks nothing of ψ off W and is meaningful when W has empty interior
--   - generalization: w_t the iterates of the algorithm → any sequence with w_0 the reference point of Assumption 2 and w_t ∈ W for t ∈ [T]; reason: the iterates of Algorithm 1 are such a sequence, so the statement specializes to the paper's
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: rounds 1, …, T (and T + 1) and finite sequences indexed by them → natural numbers and sequences ℕ → … whose terms outside the used indices are unconstrained; reason: only the paper's indices are read; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §6.3, Lemma 4, p.18; proof pp.18–19

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF
import Definitions.Def_DelayedGamesMAO_observed
import Definitions.Def_DelayedGamesMAO_sigmaMax
import Definitions.Def_DelayedGamesMAO_Assumption2

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Lemma 4 (the hint-anchor penalty is at most `Mσ_max`).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §6.3, Lemma 4, p.18 (proof pp.18–19): "Let Assumption 2 hold and consider any sequence
`s_1, …, s_{T+1}` satisfying the assumptions of Lemma 3. Then, for every `u ∈ W`,
`∑_{t=1}^T (D_ψ(u | w_{s_{t+1}}) − D_ψ(u | w_t)) ≤ Mσ_max`."

**Formalization Note.** `W` is the protocol's nonempty compact convex domain;
`D_ψ = TimeVaryingGames.bregman ψ dψ`. The paper's `w_t` are the iterates; the statement is
made for any sequence with `w_0` the reference point of Assumption 2 and `w_t ∈ W` for
`t ∈ [T]` (Algorithm 1's iterates are one). The hypotheses on `s` are Lemma 3's; the
protocol's `t + d_t ≤ T` is a hypothesis. -/
theorem lemma_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Set E) (hWne : W.Nonempty) (hWc : IsCompact W) (hWcv : Convex ℝ W)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (w0 : E) (M : ℝ) (hA2 : Assumption2 W ψ dψ w0 M)
    (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (s : ℕ → ℕ)
    (hs : ∀ t ∈ Finset.Icc 1 (T + 1),
      (observed d t \ (Finset.Icc 1 (t - 1)).image s).Nonempty →
        s t ∈ observed d t \ (Finset.Icc 1 (t - 1)).image s)
    (hs0 : ∀ t ∈ Finset.Icc 1 (T + 1),
      observed d t \ (Finset.Icc 1 (t - 1)).image s = ∅ → s t = 0)
    (w : ℕ → E) (hw0 : w 0 = w0) (hw : ∀ t ∈ Finset.Icc 1 T, w t ∈ W) :
    ∀ u ∈ W, ∑ t ∈ Finset.Icc 1 T,
        (TimeVaryingGames.bregman ψ dψ u (w (s (t + 1))) - TimeVaryingGames.bregman ψ dψ u (w t)) ≤
      M * (sigmaMax d T : ℝ) := by sorry

end DelayedGamesMAO
