-- Prove2me | Theorems.Thm_DelayedGamesMAO_theorem_6
-- name    : DelayedGamesMAO.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:25:39.995914+00:00
-- url     : https://prove2.me/theorems/1d6e281c-8364-42a2-a7ae-2956b34b4e87
-- title:
--   Theorem 6 — regret of the multi-anchor optimistic update (13)
-- statement:
--   Let $W$ be a nonempty compact convex subset of a finite-dimensional real normed space, $\psi$ differentiable and 1-strongly convex with respect to $\|\cdot\|$ on $W$, $T\ge1$, and $(d_t)$ delays with $t+d_t\le T$. Let $(g_t)$ be gradients, $h_1,\dots,h_{T+1}$ hints with $h_1=h_{T+1}=0$, and $c^{(t+1)}_k\ge0$ ($0\le k\le t\le T$) with $c^{(1)}_0>0$ and $c^{(t+d_t+1)}_t>0$ for every $t\in[T]$. Let $w_1,\dots,w_{T+1}$ be given by (MAO) from $w_0\in W$:
--   $$
--   w_{t+1}\in\arg\min_{w\in W}\Bigl\{\Bigl\langle h_{t+1}+\sum_{s\in N_t}(g_s-h_s),w\Bigr\rangle+\sum_{s=0}^tc^{(t+1)}_sD_\psi(w\mid w_s)\Bigr\}\quad(t=0,\dots,T).
--   $$
--   Then for every $u\in W$,
--   $$
--   \sum_{t=1}^T\langle g_t,w_t-u\rangle\le A^{\mathrm{out}}_0D_\psi(u\mid w_0)+\sum_{t=1}^T\bigl(A^{\mathrm{out}}_t-A^{\mathrm{in}}_t\bigr)D_\psi(u\mid w_t)+\sum_{t=1}^T\frac{\|g_t-h_t\|_*^2}{c^{(t+d_t+1)}_t}-\frac12\sum_{t=0}^T\sum_{k=0}^tc^{(t+1)}_kD_\psi(w_{t+1}\mid w_k).
--   $$
--
--   The prediction error of round $t$ is paid by the weight $c^{(t+d_t+1)}_t$ set when its feedback arrives, not by the weight of the next round; this is what allows delay-adaptive rates.
--
--   Differences from the source:
--   - encoding: W ⊆ ℝⁿ with a norm ‖·‖ and dual norm ‖·‖∗; gradients and hints in ℝⁿ → a finite-dimensional real normed space E; gradients and hints are continuous linear functionals E →L[ℝ] ℝ with the operator norm; reason: ℝⁿ with any norm is such a space and every such space is ℝⁿ with a norm; the operator norm is the dual norm; same instances
--   - generalization: ψ differentiable on W with gradient ∇ψ, and D_ψ(u | w) = ψ(u) − ψ(w) − ⟨∇ψ(w), u − w⟩ → a derivative field dψ of ψ within W (IsGradientOn) and D_ψ = TimeVaryingGames.bregman ψ dψ; reason: the gradient of a differentiable ψ is such a field, so the statement specializes to the paper's; it asks nothing of ψ off W and is meaningful when W has empty interior
--   - generalization: ψ : W → ℝ≥0 → ψ real-valued (nonnegativity not required); reason: a nonnegative ψ is a special case, so the statement specializes to the paper's
--   - encoding: w_{t+1} ∈ arg min_{w∈W} {…} → w_{t+1} ∈ W and its objective value is at most that of every v ∈ W; reason: the definition of a minimizer; same instances
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: rounds 1, …, T (and T + 1) and finite sequences indexed by them → natural numbers and sequences ℕ → … whose terms outside the used indices are unconstrained; reason: only the paper's indices are read; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §6.2, Theorem 6, eq. (13), p.15

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF
import Definitions.Def_DelayedGamesMAO_IsGradientOn
import Definitions.Def_DelayedGamesMAO_IsOneStronglyConvex
import Definitions.Def_DelayedGamesMAO_Ain
import Definitions.Def_DelayedGamesMAO_Aout
import Definitions.Def_DelayedGamesMAO_optLoss
import Definitions.Def_DelayedGamesMAO_IsMultiAnchorRun

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Theorem 6 (regret of the multi-anchor optimistic update rule).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §6.2, Theorem 6, eq. (13), p.15: "Fix hints `(h_t)_{t=1}^{T+1}` from `ℝⁿ` with
`h_1 = h_{T+1} = 0` and anchor weights `(c_k^{(t+1)})_{0≤k≤t≤T}` from `[0, ∞)` with
`c_0^{(1)} > 0` and `c_t^{(t+d_t+1)} > 0` for every `t ∈ [T]`, and let `w_1, …, w_{T+1}` be given
by (MAO) from `w_0 ∈ W`, where `ψ : W → ℝ_{≥0}` is 1-strongly convex w.r.t. `‖·‖`. Then, for every
`u ∈ W`, `∑_{t=1}^T ⟨g_t, w_t − u⟩ ≤ A_0^{out} D_ψ(u | w_0) + ∑_{t=1}^T (A_t^{out} − A_t^{in}) D_ψ(u | w_t)
+ ∑_{t=1}^T ‖g_t − h_t‖_*² / c_t^{(t+d_t+1)} − ½ ∑_{t=0}^T ∑_{k=0}^t c_k^{(t+1)} D_ψ(w_{t+1} | w_k)`."

(MAO), p.9: `w_{t+1} ∈ arg min_{w∈W} {⟨h_{t+1} + ∑_{s∈N_t}(g_s − h_s), w⟩ + ∑_{s=0}^t c_s^{(t+1)} D_ψ(w | w_s)}`.

**Formalization Note.** `W` is the protocol's nonempty compact convex domain; `g t` is the
(arbitrary) gradient of round `t`; `c t k = c_k^{(t)}`. `ψ`'s gradient is a derivative field
`dψ` within `W`, `D_ψ = TimeVaryingGames.bregman ψ dψ`, and 1-strong convexity is
`IsOneStronglyConvex`. The codomain `ℝ_{≥0}` of `ψ` is not imposed. (MAO) is
`IsMultiAnchorRun` with loss vectors `optLoss d g h`. The protocol's `t + d_t ≤ T` is a
hypothesis. -/
theorem theorem_6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Set E) (hWne : W.Nonempty) (hWc : IsCompact W) (hWcv : Convex ℝ W)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (hψd : IsGradientOn W ψ dψ)
    (hψs : IsOneStronglyConvex W ψ dψ)
    (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (g h : ℕ → E →L[ℝ] ℝ) (hh1 : h 1 = 0) (hhT : h (T + 1) = 0)
    (c : ℕ → ℕ → ℝ) (hc : ∀ t ∈ Finset.range (T + 1), ∀ k ∈ Finset.range (t + 1), 0 ≤ c (t + 1) k)
    (hc0 : 0 < c 1 0) (hcd : ∀ t ∈ Finset.Icc 1 T, 0 < c (t + d t + 1) t)
    (w0 : E) (hw0 : w0 ∈ W) (w : ℕ → E) (hw : IsMultiAnchorRun W ψ dψ w0 T (optLoss d g h) c w) :
    ∀ u ∈ W, ∑ t ∈ Finset.Icc 1 T, g t (w t - u) ≤
      Aout c T 0 * TimeVaryingGames.bregman ψ dψ u w0 +
        ∑ t ∈ Finset.Icc 1 T, (Aout c T t - Ain c t) * TimeVaryingGames.bregman ψ dψ u (w t) +
        ∑ t ∈ Finset.Icc 1 T, ‖g t - h t‖ ^ 2 / c (t + d t + 1) t -
        (1 / 2 : ℝ) * ∑ t ∈ Finset.range (T + 1), ∑ k ∈ Finset.range (t + 1),
          c (t + 1) k * TimeVaryingGames.bregman ψ dψ (w (t + 1)) (w k) := by sorry

end DelayedGamesMAO
