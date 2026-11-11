-- Prove2me | Theorems.Thm_FlexRigidity_lemma_2_9
-- name    : FlexRigidity.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:21:54.819816+00:00
-- url     : https://prove2.me/theorems/628ba146-ce7f-40f8-8a0e-2d2186acd944
-- title:
--   Lemma 2.9 — probability transfer from $D_\alpha$ and from $D^\varepsilon_{\max}$
-- statement:
--   Let $\rho$ be a normalized state, $\sigma$ a PSD operator and $0\le H\le I$ an effect.
--
--   1. If $D_\alpha(\rho\|\sigma)\le d$ for some $\alpha>1$, then
--   $$\operatorname{Tr}[H\rho]\le\big(2^d\operatorname{Tr}[H\sigma]\big)^{(\alpha-1)/\alpha}.$$
--   2. If $D^\varepsilon_{\max}(\rho\|\sigma)\le d$, then $\operatorname{Tr}[H\rho]\le2^d\operatorname{Tr}[H\sigma]+\varepsilon$.
--
--   Here $D_\alpha$ is the sandwiched Rényi divergence and $D^\varepsilon_{\max}$ the smooth max-divergence (log base 2). The lemma converts a divergence bound between a real and an ideal state into a bound on event probabilities; clause 1 is the final step of the proof of Theorem 5.6.
--
--   **Formalization Note** In clause 2, $\varepsilon$ ranges over $[0,1)=[0,\sqrt{\operatorname{Tr}\rho})$, the domain of Definition 2.9.
--
--   Differences from the source:
--   - encoding: D^ε_max defined for ε ∈ [0, √Tr ρ) (Definition 2.9) → clause (ii) assumes 0 ≤ ε < 1; reason: Tr ρ = 1; the condition only excludes values where D^ε_max is undefined
--   - encoding: divergences and channel divergences with values in [0, +∞] → values in EReal (extended reals); reason: Lean convention; the +∞ conventions of Definition 2.7 are kept, no instance changes
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 2.9, p. 21

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_smoothMaxDiv
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 2.9 (Probability transfer)** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, p. 21). Let `ρ` be normalized, `σ` PSD and `0 ≤ H ≤ I`.
(i) If `D_α(ρ‖σ) ≤ d` for some `α > 1`, then `Tr[Hρ] ≤ (2^d Tr[Hσ])^{(α−1)/α}`.
(ii) If `D^ε_max(ρ‖σ) ≤ d`, then `Tr[Hρ] ≤ 2^d Tr[Hσ] + ε`.

**Formalization Note** `D_α` is the reused `Dependency50.P35.divergence` (base 2). In (ii) `ε` is in
the domain `[0, √Tr ρ) = [0, 1)` of Definition 2.9. -/
theorem lemma_2_9 {I : Type} [Fintype I] [DecidableEq I] (ρ σ H : Matrix I I ℂ)
    (hρ : Density ρ) (hσ : σ.PosSemidef) (hH : H.PosSemidef ∧ (1 - H).PosSemidef) :
    (∀ α d : ℝ, 1 < α → divergence α ρ σ ≤ (d : EReal) →
      tr (H * ρ) ≤ ((2 : ℝ) ^ d * tr (H * σ)) ^ ((α - 1) / α)) ∧
    (∀ ε d : ℝ, 0 ≤ ε → ε < 1 → smoothMaxDiv ε ρ σ ≤ (d : EReal) →
      tr (H * ρ) ≤ (2 : ℝ) ^ d * tr (H * σ) + ε) := by sorry

end FlexRigidity
