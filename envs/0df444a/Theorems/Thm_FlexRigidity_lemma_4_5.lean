-- Prove2me | Theorems.Thm_FlexRigidity_lemma_4_5
-- name    : FlexRigidity.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:21:08.875766+00:00
-- url     : https://prove2.me/theorems/33c702fc-946c-483b-beb5-3ac38714470b
-- title:
--   Lemma 4.5 — depolarized pure-state comparison
-- statement:
--   Let $\rho_{SQ}$ be a normalized state and $|\phi\rangle_S$ a normalized pure state, with $|S|>1$ and $0<\mu<1$. Put
--   $$\omega^\mu_S=(1-\mu)|\phi\rangle\langle\phi|_S+\mu\frac{I_S}{|S|},\qquad a_\mu=1-\mu+\frac\mu{|S|},\qquad\eta=1-\langle\phi|\rho_S|\phi\rangle.$$
--   Then $D_{\max}(\rho_{SQ}\|\omega^\mu_S\otimes\rho_Q)\le\log(|S|^2/\mu)$, and for every $\alpha>1$,
--   $$D_\alpha(\rho_{SQ}\|\omega^\mu_S\otimes\rho_Q)\le\frac\alpha{\alpha-1}\log\Big[a_\mu^{-(\alpha-1)/\alpha}(1-\eta)^{1/\alpha}+\Big(\frac{|S|(|S|-1)}{\mu}\Big)^{(\alpha-1)/\alpha}\eta^{1/\alpha}\Big].$$
--   The bounds do not depend on $|Q|$. They show that depolarizing an ideal pure state makes the comparison with it finite, which is what the replacement channels of §5 need.
--
--   Differences from the source:
--   - encoding: divergences and channel divergences with values in [0, +∞] → values in EReal (extended reals); reason: Lean convention; the +∞ conventions of Definition 2.7 are kept, no instance changes
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 4.5, pp. 35–36

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_depol
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_FlexRigidity_aMu
import Definitions.Def_DHRUniq_IsUnitVec
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 4.5 (Depolarized pure-state comparison)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, pp. 35–36). Let `ρ_{SQ}` and pure `|ϕ⟩_S` be
normalized, `|S| > 1`, `0 < µ < 1`, `ω^µ_S = (1−µ)|ϕ⟩⟨ϕ|_S + µ I_S/|S|`, `a_µ = 1 − µ + µ/|S|`,
`η = 1 − ⟨ϕ|ρ_S|ϕ⟩`. Then `D_max(ρ_{SQ}‖ω^µ_S ⊗ ρ_Q) ≤ log(|S|²/µ)`, and for every `α > 1`,
`D_α(ρ_{SQ}‖ω^µ_S ⊗ ρ_Q) ≤ (α/(α−1)) log[ a_µ^{−(α−1)/α}(1−η)^{1/α} + (|S|(|S|−1)/µ)^{(α−1)/α} η^{1/α} ]`.
`Q` is arbitrary: the bound does not depend on `|Q|`.

**Formalization Note** `ρ_S`, `ρ_Q` are `leftMarginal`, `rightMarginal`; `⟨ϕ|ρ_S|ϕ⟩` is the real
part of `Σ conj(ϕ_s) (ρ_S)_{ss′} ϕ_{s′}`; logs base 2, real powers `rpow`. -/
theorem lemma_4_5 {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
    (ρ : Matrix (S × Q) (S × Q) ℂ) (hρ : Density ρ) (ϕ : S → ℂ) (hϕ : DHRUniq.IsUnitVec ϕ)
    (hS : 1 < Fintype.card S) (μ : ℝ) (hμ : 0 < μ ∧ μ < 1) :
    let ωμ := depol μ (ObliviousRSP.pureState ϕ)
    let s : ℝ := Fintype.card S
    let a := aMu μ s
    let η := 1 - (∑ x, ∑ x', star (ϕ x) * leftMarginal ρ x x' * ϕ x').re
    maxRelative ρ (Matrix.kronecker ωμ (rightMarginal ρ)) ≤ ((Real.logb 2 (s ^ 2 / μ) : ℝ) : EReal) ∧
    ∀ α : ℝ, 1 < α → divergence α ρ (Matrix.kronecker ωμ (rightMarginal ρ)) ≤
      (((α / (α - 1)) * Real.logb 2 (a ^ (-(α - 1) / α) * (1 - η) ^ (1 / α) +
        (s * (s - 1) / μ) ^ ((α - 1) / α) * η ^ (1 / α)) : ℝ) : EReal) := by sorry

end FlexRigidity
