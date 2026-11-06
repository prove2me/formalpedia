-- Prove2me | Theorems.Thm_DelayedGamesMAO_theorem_5
-- name    : DelayedGamesMAO.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:32:38.074118+00:00
-- url     : https://prove2.me/theorems/e7f710f4-8e11-4b64-b91a-26e775acf111
-- title:
--   Theorem 5 — master bound for Algorithm 1
-- statement:
--   Let $W$ be a nonempty compact convex subset of a finite-dimensional real normed space, $\psi$ differentiable and 1-strongly convex with respect to $\|\cdot\|$ on $W$, $w_0\in W$ with $D_\psi(u\mid w_0)\le M$ for every $u\in W$. Let $T\ge1$, $(d_t)$ delays with $t+d_t\le T$, $\gamma>0$, $\alpha$ an allocation schedule and $0=\eta_1\le\dots\le\eta_{T+1}$. For every gradient sequence $(g_t)$ and every run $(w_t)$ of Algorithm 1 with these parameters, and every $u\in W$,
--   $$
--   \sum_{t=1}^T\langle g_t,w_t-u\rangle\le2\gamma Mq_{\max}+M\eta_{T+1}+\sum_{t=1}^T\frac{\|g_t-h_t\|_*^2}{\gamma+\eta_t\alpha^{(t+d_t)}_t}-\frac\gamma4\sum_{t=1}^T\|w_{t+1}-w_{s_{t+1}}\|^2 ,
--   $$
--   where $h_t$ are the hints and $s_t$ the hint sources.
--
--   The bound holds for any allocation schedule and any nondecreasing learning rates; Theorem 1 specializes it to (9) and (10).
--
--   Differences from the source:
--   - encoding: W ⊆ ℝⁿ with a norm ‖·‖ and dual norm ‖·‖∗; gradients and hints in ℝⁿ → a finite-dimensional real normed space E; gradients and hints are continuous linear functionals E →L[ℝ] ℝ with the operator norm; reason: ℝⁿ with any norm is such a space and every such space is ℝⁿ with a norm; the operator norm is the dual norm; same instances
--   - generalization: ψ differentiable on W with gradient ∇ψ, and D_ψ(u | w) = ψ(u) − ψ(w) − ⟨∇ψ(w), u − w⟩ → a derivative field dψ of ψ within W (IsGradientOn) and D_ψ = TimeVaryingGames.bregman ψ dψ; reason: the gradient of a differentiable ψ is such a field, so the statement specializes to the paper's; it asks nothing of ψ off W and is meaningful when W has empty interior
--   - encoding: w_{t+1} ∈ arg min_{w∈W} {…} → w_{t+1} ∈ W and its objective value is at most that of every v ∈ W; reason: the definition of a minimizer; same instances
--   - encoding: Q_{T+1}, used through β_{T+1} in (8), undefined → Q_t = max_{s∈[t]} q_s for every t (= Q_T at T + 1); reason: the value Q_{T+1} = q_max that the proof uses
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: rounds 1, …, T (and T + 1) and finite sequences indexed by them → natural numbers and sequences ℕ → … whose terms outside the used indices are unconstrained; reason: only the paper's indices are read; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, Theorem 5, p.11; proof §6.3, pp.21–22

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF
import Definitions.Def_DelayedGamesMAO_IsGradientOn
import Definitions.Def_DelayedGamesMAO_IsOneStronglyConvex
import Definitions.Def_DelayedGamesMAO_IsAllocationSchedule
import Definitions.Def_DelayedGamesMAO_qmax
import Definitions.Def_DelayedGamesMAO_IsAlg1Run

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Theorem 5 (master bound).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, Theorem 5, p.11 (restated and proved pp.21–22): "Let `ψ` be differentiable and
1-strongly convex with respect to `‖·‖`, with `sup_{u∈W} D_ψ(u | w_0) ≤ M` for every `u ∈ W`.
Let `γ > 0`, let `(α_k^{(t)})_{1≤k≤t≤T+1}` be an allocation schedule, and let
`0 = η_1 ≤ ⋯ ≤ η_{T+1}`. Then Algorithm 1 guarantees, for every `u ∈ W`,
`∑_{t=1}^T ⟨g_t, w_t − u⟩ ≤ 2γMq_max + Mη_{T+1} + ∑_{t=1}^T ‖g_t − h_t‖_*² / (γ + η_t α_t^{(t+d_t)})
− (γ/4) ∑_{t=1}^T ‖w_{t+1} − w_{s_{t+1}}‖²`."

**Formalization Note.** `W` is the protocol's nonempty compact convex domain, `w_0 ∈ W`
Algorithm 1's reference point, `g t` the (arbitrary) gradient of round `t`. The run is
`IsAlg1Run` with the given `γ, α, η`; `h_t = hint d T g t`, `s_t = hintSrc d t`,
`α t s = α_s^{(t)}`. `ψ`'s gradient is a derivative field `dψ` within `W`;
`D_ψ = TimeVaryingGames.bregman ψ dψ`. The protocol's `t + d_t ≤ T` is a hypothesis. -/
theorem theorem_5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Set E) (hWne : W.Nonempty) (hWc : IsCompact W) (hWcv : Convex ℝ W)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (hψd : IsGradientOn W ψ dψ)
    (hψs : IsOneStronglyConvex W ψ dψ) (w0 : E) (hw0 : w0 ∈ W) (M : ℝ)
    (hM : ∀ u ∈ W, TimeVaryingGames.bregman ψ dψ u w0 ≤ M)
    (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (γ : ℝ) (hγ : 0 < γ) (α : ℕ → ℕ → ℝ) (hα : IsAllocationSchedule d T α)
    (η : ℕ → ℝ) (hη1 : η 1 = 0) (hηmono : ∀ t ∈ Finset.Icc 1 T, η t ≤ η (t + 1))
    (g : ℕ → E →L[ℝ] ℝ) (w : ℕ → E) (hw : IsAlg1Run W ψ dψ w0 γ T d α η g w) :
    ∀ u ∈ W, ∑ t ∈ Finset.Icc 1 T, g t (w t - u) ≤
      2 * γ * M * (qmax d T : ℝ) + M * η (T + 1) +
        ∑ t ∈ Finset.Icc 1 T, ‖g t - hint d T g t‖ ^ 2 / (γ + η t * α (t + d t) t) -
        γ / 4 * ∑ t ∈ Finset.Icc 1 T, ‖w (t + 1) - w (hintSrc d (t + 1))‖ ^ 2 := by sorry

end DelayedGamesMAO
