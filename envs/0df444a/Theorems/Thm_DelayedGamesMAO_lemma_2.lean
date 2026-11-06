-- Prove2me | Theorems.Thm_DelayedGamesMAO_lemma_2
-- name    : DelayedGamesMAO.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:44.181933+00:00
-- url     : https://prove2.me/theorems/a72c6484-0535-45b4-a146-3153054a67d1
-- title:
--   Lemma 2 — multi-anchor three-point inequality
-- statement:
--   Let $W$ be a nonempty compact convex subset of a finite-dimensional real normed space, $\ell$ a dual vector, $z_1,\dots,z_k\in W$, $\alpha_1,\dots,\alpha_k\ge0$, and $\psi$ convex and differentiable on $W$. Let $A=\sum_i\alpha_i$ and
--   $$
--   w\in\arg\min_{x\in W}\Bigl\{\langle\ell,x\rangle+\sum_{i=1}^k\alpha_iD_\psi(x\mid z_i)\Bigr\}.
--   $$
--   Then for every $u\in W$,
--   $$
--   \langle\ell,w-u\rangle\le\sum_{i=1}^k\alpha_i\bigl(D_\psi(u\mid z_i)-D_\psi(w\mid z_i)\bigr)-A\,D_\psi(u\mid w).
--   $$
--
--   This generalizes the three-point inequality of mirror descent to several anchors; it is the one-step inequality behind Proposition 2.
--
--   Differences from the source:
--   - encoding: W ⊆ ℝⁿ with a norm ‖·‖ and dual norm ‖·‖∗; gradients and hints in ℝⁿ → a finite-dimensional real normed space E; gradients and hints are continuous linear functionals E →L[ℝ] ℝ with the operator norm; reason: ℝⁿ with any norm is such a space and every such space is ℝⁿ with a norm; the operator norm is the dual norm; same instances
--   - generalization: ψ differentiable on W with gradient ∇ψ, and D_ψ(u | w) = ψ(u) − ψ(w) − ⟨∇ψ(w), u − w⟩ → a derivative field dψ of ψ within W (IsGradientOn) and D_ψ = TimeVaryingGames.bregman ψ dψ; reason: the gradient of a differentiable ψ is such a field, so the statement specializes to the paper's; it asks nothing of ψ off W and is meaningful when W has empty interior
--   - encoding: w_{t+1} ∈ arg min_{w∈W} {…} → w_{t+1} ∈ W and its objective value is at most that of every v ∈ W; reason: the definition of a minimizer; same instances
--   - encoding: anchors z_1, …, z_k → anchors indexed by Fin k; reason: same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §6.1, Lemma 2, p.13

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF
import Definitions.Def_DelayedGamesMAO_IsGradientOn

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Lemma 2 (multi-anchor three-point inequality).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §6.1, Lemma 2, p.13: "Let `ℓ ∈ ℝⁿ`, let `z_1, …, z_k ∈ W`, and let `α_1, …, α_k ≥ 0`. Let
`ψ : W → ℝ` be a convex differentiable function. Define `A := ∑_{i=1}^k α_i` and
`w ∈ arg min_{x∈W} {⟨ℓ, x⟩ + ∑_{i=1}^k α_i D_ψ(x | z_i)}`. Then, for every `u ∈ W`,
`⟨ℓ, w − u⟩ ≤ ∑_{i=1}^k α_i (D_ψ(u | z_i) − D_ψ(w | z_i)) − A D_ψ(u | w)`."

**Formalization Note.** `W` is the protocol's nonempty compact convex domain in a
finite-dimensional real normed space. "Differentiable" is a derivative field `dψ` of `ψ` within
`W` (`IsGradientOn`), and `D_ψ = TimeVaryingGames.bregman ψ dψ`. The anchors are indexed by
`Fin k`; `w ∈ arg min` is "`w ∈ W` and its objective value is at most that of every
`x ∈ W`". -/
theorem lemma_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Set E) (hWne : W.Nonempty) (hWc : IsCompact W) (hWcv : Convex ℝ W)
    (ℓ : E →L[ℝ] ℝ) {k : ℕ} (z : Fin k → E) (hz : ∀ i, z i ∈ W)
    (α : Fin k → ℝ) (hα : ∀ i, 0 ≤ α i)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (hψc : ConvexOn ℝ W ψ) (hψd : IsGradientOn W ψ dψ)
    (w : E) (hw : w ∈ W)
    (hmin : ∀ x ∈ W, ℓ w + ∑ i, α i * TimeVaryingGames.bregman ψ dψ w (z i) ≤
      ℓ x + ∑ i, α i * TimeVaryingGames.bregman ψ dψ x (z i)) :
    ∀ u ∈ W, ℓ (w - u) ≤
      ∑ i, α i * (TimeVaryingGames.bregman ψ dψ u (z i) - TimeVaryingGames.bregman ψ dψ w (z i)) -
        (∑ i, α i) * TimeVaryingGames.bregman ψ dψ u w := by sorry

end DelayedGamesMAO
