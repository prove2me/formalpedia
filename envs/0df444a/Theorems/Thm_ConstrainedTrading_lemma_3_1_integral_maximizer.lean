-- Prove2me | Theorems.Thm_ConstrainedTrading_lemma_3_1_integral_maximizer
-- name    : ConstrainedTrading.lemma_3_1_integral_maximizer
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:28.650617+00:00
-- url     : https://prove2.me/theorems/44543230-48c5-438f-a235-87cadc5f51ab
-- title:
--   Lemma 3.1 (corrected: an integral maximizer exists) — $\hat w_1(x)+\hat w_2(-x)$ over an integral polymatroid
-- statement:
--   Let $E$ be a finite set, $w_1:\mathbb Z^E\to\mathbb R\cup\{-\infty\}$ M$^\sharp$-concave, $w_2(y)=\sum_{e}c_e y_e$ linear, and $P=P(\rho)$ a nonempty integral polymatroid. Then the maximum of
--   $$
--   \hat w_1(x)+\hat w_2(-x)
--   $$
--   over $x\in P$ is attained at an integral point: there is $z\in\mathbb Z^E\cap P$ with $\hat w_1(x)+\hat w_2(-x)\le\hat w_1(z)+\hat w_2(-z)$ for every $x\in P$.
--
--   This is the one-buyer, one-seller case of §3 (agent 1 with M$^\sharp$-concave $w_1$, agent 2 with linear $w_2$, net flows $y^1=-y^2=x$); Theorem 3.1 reduces the general two-sided network to it.
--
--   **Formalization Note** Hats are `concaveExt`; the sum is in `EReal`.
--
--   Differences from the source:
--
--   - correction: The maximizer(s) … over x ∈ P are integral → an integral maximizer exists (the maximum is attained at an integer point of P); reason: read as 'every maximizer is integral' it is false: E = {e}, w₁ ≡ w₂ ≡ 0, P = [0,1], every x ∈ [0,1] (e.g. 1/2) is a maximizer; the proof shows that an extreme point attains the optimum
--   - reading: w linear → w(y) = Σ_e c_e y_e with a coefficient vector c (no constant term); reason: the strict sense of 'linear'
--   - reading: integral polymatroid P_f = {x ∈ ℝ^E : Σ_{e∈S} x_e ≤ f(S) ∀S ⊆ E} (p.4, no sign constraint) → P(ρ) = {x : x ≥ 0, Σ_{e∈S} x_e ≤ ρ(S) ∀S}; reason: standard meaning of polymatroid, outcomes are x ∈ ℤ₊^E (p.3); without x ≥ 0 the statement is false (E = {e}, ρ ≡ 0, seller valuation w(z) = −z: the objective −x is unbounded on (−∞, 0])
--   - reading: concave extension f̂(x) = max{Σ_z λ_z f(z) : Σ_z λ_z z = x, 0 ≤ λ_z ≤ 1, Σ_z λ_z = 1} (Defs 2.8–2.9, p.5) → f̂(x) = sSup over finite convex representations in EReal, sup ∅ = −∞; reason: a max need not be attained for a general f; the sup is the total version, and it is the convex-combination hull, not the closed concave closure
--   - encoding: an integral polymatroid P → hypothesis P(ρ) nonempty; reason: nondegeneracy: it only excludes P = ∅ (some ρ(S) < 0), where there is no feasible point to exhibit; when P ≠ ∅, 0 ∈ P
--   - reading: M♯-concave f : ℤ^E → R, exchange 'for all x, y ∈ B' with B unnamed (Def 2.7, p.4; p.5) → f : ℤ^E → ℝ ∪ {−∞}, exchange for x, y ∈ dom f = {z : f z ≠ −∞}; reason: the paper's valuations take values in ℝ ∪ {−∞} (p.3, footnote 3) and p.5 defines dom f; the real-valued case is dom f = ℤ^E
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Lemma 3.1, p.8; setup of §3, p.7

import Mathlib
import Definitions.Def_ConstrainedTrading_MNatConcave
import Definitions.Def_ConstrainedTrading_concaveExt
import Definitions.Def_ConstrainedTrading_linearValuation
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Definitions.Def_ConstrainedTrading_polymatroid

namespace ConstrainedTrading

/-- **Lemma 3.1** (Kizilkale–Vohra, *Constrained Trading Networks*, arXiv:2008.09757v1, p.8;
corrected: an integral maximizer exists). Let `w₁ : ℤ^E → ℝ ∪ {−∞}` be M♯-concave, let
`w₂(y) = Σ_e c_e y_e` be linear, and let `P = P(ρ)` be a nonempty integral polymatroid. Then
`ŵ₁(x) + ŵ₂(−x)` attains its maximum over `x ∈ P` at an integral point.

**Formalization Note** Hats are `concaveExt`; the sum is in `EReal` (`⊥ + a = ⊥`). The page
says "The maximizer(s) … over x ∈ P are integral"; read as "every maximizer is integral" it is
false (`E = {e}`, `w₁ ≡ w₂ ≡ 0`, `P = [0,1]`: every point of `[0,1]` is a maximizer), and the
proof shows that an extreme point attains the optimum. The conclusion asserts attainment and
integrality. `P(ρ)` includes `x ≥ 0` (reading R1). -/
theorem lemma_3_1_integral_maximizer {E : Type*} [Fintype E] [DecidableEq E]
    (w1 : (E → ℤ) → WithBot ℝ) (hw1 : MNatConcave w1) (c : E → ℝ)
    (ρ : Finset E → ℤ) (hρ : SteinitzExchange.Duality.IsSubmodular ρ) (hP : (polymatroid ρ).Nonempty) :
    ∃ z : E → ℤ, (fun e => (z e : ℝ)) ∈ polymatroid ρ ∧
      ∀ x ∈ polymatroid ρ,
        concaveExt w1 x + concaveExt (linearValuation c) (-x) ≤
          concaveExt w1 (fun e => (z e : ℝ)) +
            concaveExt (linearValuation c) (-(fun e => (z e : ℝ))) := by sorry

end ConstrainedTrading
