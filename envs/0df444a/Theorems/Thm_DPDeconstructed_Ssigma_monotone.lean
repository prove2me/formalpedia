-- Prove2me | Theorems.Thm_DPDeconstructed_Ssigma_monotone
-- name    : DPDeconstructed.Ssigma_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:38.413243+00:00
-- url     : https://prove2.me/theorems/23ee6259-5043-423e-ac3e-686e0a0c67db
-- title:
--   Proof of Theorem 3.3, p.28 — $S_\sigma$ is monotone (corrected: $W_0$, $W_1$ monotone on $\mathcal V$, $\mathcal G$)
-- statement:
--   Let $(W_0,W_1)$ be a plan factorization of a dynamic program with $W_0$ monotone on $\mathcal V$ and $W_1$ monotone on $\mathcal G$ (pointwise orders). Then for every feasible policy $\sigma$ the refactored $\sigma$-value operator $S_\sigma=W_0M_\sigma W_1$ is monotone on $\mathcal G$:
--
--   $$g\le g'\ \text{ in }\mathcal G\quad\Longrightarrow\quad S_\sigma g\le S_\sigma g'.$$
--
--   It is the step of the proof of Theorem 3.3 that lets the inequality $\bar g\ge S_\sigma\bar g$ be iterated to $\bar g\ge S_\sigma^k\bar g$.
--
--   Differences from the source:
--   - generalization: S_σ is monotone on 𝔾 (under the hypotheses of Theorem 3.3) → S_σ is monotone on 𝒢, assuming only the plan factorization and the two monotonicity hypotheses; reason: 𝔾 ⊆ 𝒢, and the proof iterates S_σ at points of 𝒢 outside 𝔾; monotonicity on 𝒢 implies the printed claim
--   - correction: W₀ and W₁ are monotone (p.14: with respect to the pointwise order on 𝕍, 𝔾 and ℍ) → W₀ is monotone on 𝒱 and W₁ is monotone on 𝒢 (MonotoneOn); reason: the printed domains make the statement false: X = {x}, Γ(x) = {a, b}, 𝒱 = ℝ, H(x,a,v) = 1, H(x,b,v) = v/2 − 10, 𝕍 = {1, 2}, ψ the identity of ℝ with −9.5 and −9 swapped, W₀v = (ψv, ψv), W₁(s, t) = (1, ψs/2 − 10) satisfies every assumption of Theorem 3.3 with W₀ monotone on 𝕍 and W₁ on 𝔾, yet S_{σ_b}(1, 1) = (−9, −9) and S_{σ_b}(2, 2) = (−9.5, −9.5); M_σ W₁ g lies in 𝒱, not in 𝕍, which is why W₀ is needed on 𝒱
--   - encoding: plan factorization: W₀ defined on 𝒱 with values in 𝒢, W₁ defined on 𝒢 with values in ℋ, and (7) → structure with total maps W₀ on ℝ^X, W₁ on ℝ^F and the single field (7); reason: 𝒢 := W₀𝒱 gives the first condition and (7) gives the second; values off 𝒱 and 𝒢 never enter a statement, so every pair on the page is an instance
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, proof of Theorem 3.3, p.28 (unnumbered: "We know that S_σ is monotone on 𝔾 …")

import Mathlib
import Definitions.Def_DPDeconstructed_PlanFactorization

namespace DPDeconstructed

open DynProg PlanFactorization

/-- Ma and Stachurski, *Dynamic Programming Deconstructed*, arXiv:1811.01940v2, proof of
Theorem 3.3, p.28 (unnumbered): "`S_σ` is monotone on `𝔾`, since this operator is the
composition of three monotone operators (`W₀` and `W₁` by assumption and `M_σ`
automatically)." Stated here on `𝒢`: if `W₀` is monotone on `𝒱` and `W₁` is monotone on `𝒢`,
then for every `σ ∈ Σ` the refactored `σ`-value operator `S_σ = W₀ M_σ W₁` is monotone on `𝒢`
(pointwise order).

**Formalization Note** The page says "on `𝔾`"; the proof iterates `S_σ` from a point of `𝔾`,
and the iterates lie in `𝒢`. Monotonicity on `𝒢 ⊇ 𝔾` implies the printed claim.
(Correction.) The hypotheses are on `𝒱` and `𝒢`, not on `𝕍` and `𝔾` as on p.14: `M_σ W₁ g` lies
in `𝒱`, not in `𝕍` in general. With monotonicity only on `𝕍` and `𝔾` the claim is false (one
state, actions `a, b`, `𝒱 = ℝ`, `H(x,a,v) = 1`, `H(x,b,v) = v/2 − 10`, `𝕍 = {1, 2}`, `ψ` the
identity of `ℝ` with `−9.5` and `−9` swapped, `W₀ v = (ψ v, ψ v)`,
`W₁(s, t) = (1, ψ s / 2 − 10)`: `S_{σ_b}(1, 1) = (−9, −9)`, `S_{σ_b}(2, 2) = (−9.5, −9.5)`). -/
theorem Ssigma_monotone {X A : Type*} [Nonempty X] (D : DynProg X A)
    (P : PlanFactorization D) (hW₀ : MonotoneOn P.W₀ D.𝒱) (hW₁ : MonotoneOn P.W₁ P.calG)
    (σ : D.Policy) :
    MonotoneOn (P.Sσ σ) P.calG := by sorry

end DPDeconstructed
