-- Prove2me | Theorems.Thm_DelayedGamesMAO_proposition_2
-- name    : DelayedGamesMAO.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:25:02.816164+00:00
-- url     : https://prove2.me/theorems/366cac9f-fb28-4f89-b09c-b45c3a033a10
-- title:
--   Proposition 2 — cheating regret of the multi-anchor update
-- statement:
--   Let $W$ be a nonempty compact convex subset of a finite-dimensional real normed space, $\psi$ differentiable on $W$, $T\ge1$ and $w_0\in W$. Let $\ell_0,\dots,\ell_T$ be dual vectors with $\ell_0=0$ and $c^{(t+1)}_k\ge0$ for $0\le k\le t\le T$, and let
--   $$
--   w_{t+1}\in\arg\min_{w\in W}\Bigl\{\langle\ell_t,w\rangle+\sum_{k=0}^tc^{(t+1)}_kD_\psi(w\mid w_k)\Bigr\}\qquad(t=0,\dots,T).
--   $$
--   With $A^{\mathrm{in}}_t=\sum_{k=0}^{t-1}c^{(t)}_k$ and $A^{\mathrm{out}}_t=\sum_{k=t}^Tc^{(k+1)}_t$ (empty sums $0$), for every $u\in W$,
--   $$
--   \sum_{t=1}^T\langle\ell_t,w_{t+1}-u\rangle\le A^{\mathrm{out}}_0D_\psi(u\mid w_0)-A^{\mathrm{in}}_{T+1}D_\psi(u\mid w_{T+1})+\sum_{t=1}^T\bigl(A^{\mathrm{out}}_t-A^{\mathrm{in}}_t\bigr)D_\psi(u\mid w_t)-\sum_{t=0}^T\sum_{k=0}^tc^{(t+1)}_kD_\psi(w_{t+1}\mid w_k).
--   $$
--
--   The bound isolates the non-telescoping multi-anchor potential $\sum_t(A^{\mathrm{out}}_t-A^{\mathrm{in}}_t)D_\psi(u\mid w_t)$, which the coefficients (8) are designed to cancel.
--
--   Differences from the source:
--   - encoding: W ⊆ ℝⁿ with a norm ‖·‖ and dual norm ‖·‖∗; gradients and hints in ℝⁿ → a finite-dimensional real normed space E; gradients and hints are continuous linear functionals E →L[ℝ] ℝ with the operator norm; reason: ℝⁿ with any norm is such a space and every such space is ℝⁿ with a norm; the operator norm is the dual norm; same instances
--   - reading: no hypothesis on ψ, while D_ψ needs ∇ψ → ψ has a derivative field dψ within W; reason: the only reading under which D_ψ is defined
--   - generalization: ψ differentiable on W with gradient ∇ψ, and D_ψ(u | w) = ψ(u) − ψ(w) − ⟨∇ψ(w), u − w⟩ → a derivative field dψ of ψ within W (IsGradientOn) and D_ψ = TimeVaryingGames.bregman ψ dψ; reason: the gradient of a differentiable ψ is such a field, so the statement specializes to the paper's; it asks nothing of ψ off W and is meaningful when W has empty interior
--   - encoding: w_{t+1} ∈ arg min_{w∈W} {…} → w_{t+1} ∈ W and its objective value is at most that of every v ∈ W; reason: the definition of a minimizer; same instances
--   - encoding: rounds 1, …, T (and T + 1) and finite sequences indexed by them → natural numbers and sequences ℕ → … whose terms outside the used indices are unconstrained; reason: only the paper's indices are read; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §6.1, Proposition 2, p.14

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF
import Definitions.Def_DelayedGamesMAO_IsGradientOn
import Definitions.Def_DelayedGamesMAO_Ain
import Definitions.Def_DelayedGamesMAO_Aout
import Definitions.Def_DelayedGamesMAO_IsMultiAnchorRun

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Proposition 2 (cheating regret).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §6.1, Proposition 2, p.14: "Fix `T ∈ ℕ₊` and `w_0 ∈ W`. Let `ℓ_0, …, ℓ_T ∈ ℝⁿ` with `ℓ_0 = 0`
and, for each `t ∈ {0, …, T}` and each `0 ≤ k ≤ t`, let `c_k^{(t+1)} ≥ 0`. For every
`t ∈ {0, …, T}` define `w_{t+1} ∈ arg min_{w∈W} {⟨ℓ_t, w⟩ + ∑_{k=0}^t c_k^{(t+1)} D_ψ(w | w_k)}`.
Also define `A_t^{in} := ∑_{k=0}^{t−1} c_k^{(t)}` and `A_t^{out} := ∑_{k=t}^T c_t^{(k+1)}` for each
`t ∈ {0, …, T + 1}`, with empty sums equal to zero. Then, for every `u ∈ W`,
`∑_{t=1}^T ⟨ℓ_t, w_{t+1} − u⟩ ≤ A_0^{out} D_ψ(u | w_0) − A_{T+1}^{in} D_ψ(u | w_{T+1})
+ ∑_{t=1}^T (A_t^{out} − A_t^{in}) D_ψ(u | w_t) − ∑_{t=0}^T ∑_{k=0}^t c_k^{(t+1)} D_ψ(w_{t+1} | w_k)`."

`c t k` is `c_k^{(t)}`.

**Formalization Note.** `W` is the protocol's nonempty compact convex domain. The proposition
puts no hypothesis on `ψ`; its Bregman divergence needs a gradient, which is a derivative field
`dψ` within `W` (`IsGradientOn`), with `D_ψ = TimeVaryingGames.bregman ψ dψ`. The update is
`IsMultiAnchorRun` (with `w 0 = w_0`). -/
theorem proposition_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Set E) (hWne : W.Nonempty) (hWc : IsCompact W) (hWcv : Convex ℝ W)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (hψd : IsGradientOn W ψ dψ)
    (T : ℕ) (hT : 1 ≤ T) (w0 : E) (hw0 : w0 ∈ W)
    (ℓ : ℕ → E →L[ℝ] ℝ) (hℓ0 : ℓ 0 = 0)
    (c : ℕ → ℕ → ℝ) (hc : ∀ t ∈ Finset.range (T + 1), ∀ k ∈ Finset.range (t + 1), 0 ≤ c (t + 1) k)
    (w : ℕ → E) (hw : IsMultiAnchorRun W ψ dψ w0 T ℓ c w) :
    ∀ u ∈ W, ∑ t ∈ Finset.Icc 1 T, ℓ t (w (t + 1) - u) ≤
      Aout c T 0 * TimeVaryingGames.bregman ψ dψ u w0 -
        Ain c (T + 1) * TimeVaryingGames.bregman ψ dψ u (w (T + 1)) +
        ∑ t ∈ Finset.Icc 1 T, (Aout c T t - Ain c t) * TimeVaryingGames.bregman ψ dψ u (w t) -
        ∑ t ∈ Finset.range (T + 1), ∑ k ∈ Finset.range (t + 1),
          c (t + 1) k * TimeVaryingGames.bregman ψ dψ (w (t + 1)) (w k) := by sorry

end DelayedGamesMAO
