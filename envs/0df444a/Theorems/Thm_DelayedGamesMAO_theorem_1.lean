-- Prove2me | Theorems.Thm_DelayedGamesMAO_theorem_1
-- name    : DelayedGamesMAO.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:34:03.264206+00:00
-- url     : https://prove2.me/theorems/0df1dbf4-4ae8-4a93-803b-dff3e3042ab3
-- title:
--   Theorem 1 — per-player guarantee of MAO-OMD
-- statement:
--   Let $W$ be a nonempty compact convex subset of a finite-dimensional real normed space and let $\psi$, $w_0$, $M$ satisfy Assumption 2. Let $G,L>0$, $T\ge1$, $(d_t)$ delays with $t+d_t\le T$, and $(g_t)$ gradients with $\|g_t\|_*\le G$ for $t\in[T]$. If $(w_t)$ and $(\eta_t)$ are a run of MAO-OMD (Algorithm 1 with the schedule (10), the tuning (9) and $\gamma=\max\{4L,2G/\sqrt M\}$), then for every $u\in W$,
--   $$
--   \sum_{t=1}^T\langle g_t,w_t-u\rangle\le\bigl(8LM+4G\sqrt M\bigr)q_{\max}+2\sqrt{2M\sum_{t=1}^T\kappa_t\|g_t-h_t\|_*^2}-L\sum_{t=1}^T\|w_t-w_{s_t}\|^2 ,
--   $$
--   where $h_t$ are the hints, $s_t$ the hint sources and $\kappa_t$ the congestion of round $t$.
--
--   Theorems 2 and 3 follow by bounding the prediction errors $\|g_t-h_t\|_*$ by smoothness in self-play and by $2G$ against an arbitrary opponent.
--
--   **Formalization Note** The paper assumes Assumption 1 for the game; the theorem uses it only through $\|g_t\|_*\le G$ and the constants $G,L>0$ in $\gamma$, which is how it is stated here for an arbitrary gradient sequence.
--
--   Differences from the source:
--   - encoding: W ⊆ ℝⁿ with a norm ‖·‖ and dual norm ‖·‖∗; gradients and hints in ℝⁿ → a finite-dimensional real normed space E; gradients and hints are continuous linear functionals E →L[ℝ] ℝ with the operator norm; reason: ℝⁿ with any norm is such a space and every such space is ℝⁿ with a norm; the operator norm is the dual norm; same instances
--   - generalization: Assumption 1 for the game, the player's gradients g_t = ∇f_t(w_t) against any opponent → an arbitrary gradient sequence with ‖g_t‖∗ ≤ G for t ∈ [T], and G, L > 0; reason: Assumption 1 gives exactly these to a player against any opponent, so the statement specializes to the paper's
--   - generalization: ψ differentiable on W with gradient ∇ψ, and D_ψ(u | w) = ψ(u) − ψ(w) − ⟨∇ψ(w), u − w⟩ → a derivative field dψ of ψ within W (IsGradientOn) and D_ψ = TimeVaryingGames.bregman ψ dψ; reason: the gradient of a differentiable ψ is such a field, so the statement specializes to the paper's; it asks nothing of ψ off W and is meaningful when W has empty interior
--   - encoding: w_{t+1} ∈ arg min_{w∈W} {…} → w_{t+1} ∈ W and its objective value is at most that of every v ∈ W; reason: the definition of a minimizer; same instances
--   - encoding: η following (9) → a sequence η satisfying the recursion (9) (IsTuning); reason: (9) determines η uniquely; same instances
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: rounds 1, …, T (and T + 1) and finite sequences indexed by them → natural numbers and sequences ℕ → … whose terms outside the used indices are unconstrained; reason: only the paper's indices are read; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, Theorem 1, p.12; proof §6.4, p.23

import Mathlib
import Definitions.Def_DelayedGamesMAO_Assumption2
import Definitions.Def_DelayedGamesMAO_qmax
import Definitions.Def_DelayedGamesMAO_kappa
import Definitions.Def_DelayedGamesMAO_IsMAOOMDRun

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Theorem 1 (the per-player guarantee of MAO-OMD).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, Theorem 1, p.12 (proof §6.4, p.23): "Let Assumption 1 hold and let `ψ : W → ℝ` and
`w_0 ∈ W` satisfy Assumption 2. Consider the allocation schedule `(α_s^{(t)})_{s≤t}` in (10) and
the sequence `0 = η_1 ≤ ⋯ ≤ η_{T+1}` following (9). Then Algorithm 1 with `γ = max{4L, 2G/√M}`
guarantees, for every `u ∈ W`, `∑_{t=1}^T ⟨g_t, w_t − u⟩ ≤ (8LM + 4G√M) q_max
+ 2 √(2M ∑_{t=1}^T κ_t ‖g_t − h_t‖_*²) − L ∑_{t=1}^T ‖w_t − w_{s_t}‖²`."

**Formalization Note.** The player's gradients `g t` are an arbitrary sequence of dual vectors
with `‖g_t‖_* ≤ G` for `t ∈ [T]`, and `G, L > 0`: this is what Assumption 1 gives a player
against any opponent, and the only use the theorem makes of it (`L` enters through `γ`).
`IsMAOOMDRun` is Algorithm 1 with (10), (9) and `γ = max{4L, 2G/√M}`; `h_t = hint d T g t`,
`s_t = hintSrc d t`, `κ_t = kappa d t`. `W` is the protocol's nonempty compact convex domain;
the protocol's `t + d_t ≤ T` is a hypothesis. -/
theorem theorem_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Set E) (hWne : W.Nonempty) (hWc : IsCompact W) (hWcv : Convex ℝ W)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (w0 : E) (M : ℝ) (hA2 : Assumption2 W ψ dψ w0 M)
    (G L : ℝ) (hG : 0 < G) (hL : 0 < L)
    (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (g : ℕ → E →L[ℝ] ℝ) (hg : ∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ G)
    (w : ℕ → E) (η : ℕ → ℝ) (hrun : IsMAOOMDRun W ψ dψ w0 M L G T d g w η) :
    ∀ u ∈ W, ∑ t ∈ Finset.Icc 1 T, g t (w t - u) ≤
      (8 * L * M + 4 * G * Real.sqrt M) * (qmax d T : ℝ) +
        2 * Real.sqrt (2 * M * ∑ t ∈ Finset.Icc 1 T, (kappa d t : ℝ) * ‖g t - hint d T g t‖ ^ 2) -
        L * ∑ t ∈ Finset.Icc 1 T, ‖w t - w (hintSrc d t)‖ ^ 2 := by sorry

end DelayedGamesMAO
