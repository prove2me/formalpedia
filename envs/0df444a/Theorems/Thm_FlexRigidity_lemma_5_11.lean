-- Prove2me | Theorems.Thm_FlexRigidity_lemma_5_11
-- name    : FlexRigidity.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:18.928009+00:00
-- url     : https://prove2.me/theorems/04333371-2b60-4320-ad83-8504f5ed9541
-- title:
--   Lemma 5.11 — properties of the cost function (corrected: $|S|\ge2$)
-- statement:
--   Let $|S|=|A||S_{\mathrm A}||S_{\mathrm B}|\ge2$. For fixed $1<\alpha<2$ and $\mu,\gamma\in(0,1)$, the function $\varepsilon\mapsto\mathrm{cost}_{\alpha,\mu}(\gamma,\varepsilon)$ of (66) is finite, continuous, and strictly increasing on $[0,(1-\gamma)/2]$. For fixed $\mu,\gamma\in(0,1)$,
--   $$\lim_{\alpha\to1^+}\mathrm{cost}_{\alpha,\mu}(\gamma,0)=(1-\gamma)\log a_\mu^{-1}.$$
--   These properties let the proof of Theorem 5.6 choose $\alpha$, $\mu$ and $\varepsilon_{\mathrm{tol}}$.
--
--   **Formalization Note** The cost depends on the game only through $\omega^*$, $|S|$ and $\mathrm{van}_{\mathsf G}$ (vanishing on $[0,\omega^*]$). Continuity and monotonicity are stated for the real value of the cost.
--
--   Differences from the source:
--   - correction: no lower bound on |S| → 2 ≤ |S| = |A||S_A||S_B|; reason: for |S| = 1 (one output, one-dimensional S_A, S_B), a_µ = 1 and the cost is identically 0 on [0, (1−γ)/2] (δ = η = 0 is optimal and every other term is ≤ 0), so it is not strictly increasing; §5.4 states a_µ ∈ (0, 1), which needs |S| ≥ 2
--   - encoding: cost finite, continuous and strictly increasing in ε → cost ≠ ±∞ on [0, (1−γ)/2], and its real value is ContinuousOn and StrictMonoOn there; reason: the cost is an extended-real sup; on the finite range the two readings agree
--   - generalization: Postulate Set 5.3 → the realization conditions and van_G vanishing on [0, ω*]; reason: the cost depends on G only through ω*, |S| and van_G
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 5.11, p. 54

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_cost
import Definitions.Def_FlexRigidity_Realization
import Definitions.Def_FlexRigidity_IsVanishing
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 5.11 (Properties of the cost function)** (corrected: `|S| ≥ 2`) (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 54). For fixed `1 < α < 2` and
`µ, γ ∈ (0, 1)`, the function `cost_{α,µ}(γ, ε)` is finite, continuous, and strictly increasing in
`ε ∈ [0, (1−γ)/2]`. For fixed `µ, γ ∈ (0, 1)`, it also satisfies
`lim_{α→1+} cost_{α,µ}(γ, 0) = (1−γ) log a_µ^{−1}`.

**Formalization Note** The cost is computed for the game `G` (through `ω*`, `|S| = |A||S_A||S_B|`
and `van_G`, vanishing on `[0, ω*]`). Continuity and monotonicity are stated for the real value
`toReal` of the (finite) cost on `[0, (1−γ)/2]`. The hypothesis `|S| ≥ 2` is the standing
`a_µ ∈ (0, 1)` of §5.4 (p. 47); for `|S| = 1` the cost is identically `0`. -/
theorem lemma_5_11 {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (van : ℝ → ℝ)
    (hG : G.IsValid) (hRz : Rz.IsPostulate53ii G) (hvan : IsVanishing van (quantumValue G))
    (hS : 2 ≤ Fintype.card (A × SA × SB)) :
    let ω := quantumValue G
    let s := Fintype.card (A × SA × SB)
    (∀ α μ γ : ℝ, 1 < α → α < 2 → 0 < μ → μ < 1 → 0 < γ → γ < 1 →
      (∀ ε ∈ Set.Icc 0 ((1 - γ) / 2), cost van ω s α μ γ ε ≠ ⊤ ∧ cost van ω s α μ γ ε ≠ ⊥) ∧
      ContinuousOn (fun ε => (cost van ω s α μ γ ε).toReal) (Set.Icc 0 ((1 - γ) / 2)) ∧
      StrictMonoOn (fun ε => (cost van ω s α μ γ ε).toReal) (Set.Icc 0 ((1 - γ) / 2))) ∧
    ∀ μ γ : ℝ, 0 < μ → μ < 1 → 0 < γ → γ < 1 →
      Tendsto (fun α => (cost van ω s α μ γ 0).toReal) (𝓝[>] 1)
        (𝓝 ((1 - γ) * Real.logb 2 (1 / aMu μ s))) := by sorry

end FlexRigidity
