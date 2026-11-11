-- Prove2me | Theorems.Thm_FlexRigidity_lemma_3_3
-- name    : FlexRigidity.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:39.992912+00:00
-- url     : https://prove2.me/theorems/cc38f04e-df20-4efd-94ae-fcea6b35a296
-- title:
--   Lemma 3.3 — $D_\alpha(\rho_{SQ}\|\omega_S\otimes\rho_Q)\le\inf_{\sigma_Q}D_{1/(2-\alpha)}(\rho_{SQ}\|\omega_S\otimes\sigma_Q)$
-- statement:
--   For every $1<\alpha<2$, every normalized state $\rho_{SQ}$ and every positive definite operator $\omega_S$ (not necessarily normalized),
--   $$D_\alpha(\rho_{SQ}\|\omega_S\otimes\rho_Q)\le\inf_{\sigma_Q\in S_=(Q)}D_{1/(2-\alpha)}(\rho_{SQ}\|\omega_S\otimes\sigma_Q),$$
--   where $\rho_Q=\operatorname{Tr}_S\rho_{SQ}$ and $D_\alpha$ is the sandwiched Rényi divergence (log base 2). It generalizes [MFSR24, Lemma 2.3] from $\omega_S=I_S$ to arbitrary positive definite $\omega_S$ and is the single-letter input of Lemma 3.4.
--
--   Differences from the source:
--   - encoding: divergences and channel divergences with values in [0, +∞] → values in EReal (extended reals); reason: Lean convention; the +∞ conventions of Definition 2.7 are kept, no instance changes
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 3.3, p. 23

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 3.3** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256
8c67699d…, p. 23). For every `1 < α < 2`, `ρ_{SQ} ∈ S_=(SQ)` and positive definite `ω_S` (not
necessarily normalized),
`D_α(ρ_{SQ}‖ω_S ⊗ ρ_Q) ≤ inf_{σ_Q ∈ S_=(Q)} D_{1/(2−α)}(ρ_{SQ}‖ω_S ⊗ σ_Q)`.

**Formalization Note** `ρ_Q = Tr_S ρ_{SQ}` is `rightMarginal`; the infimum is an `EReal` infimum
over normalized density matrices. -/
theorem lemma_3_3 {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
    (α : ℝ) (hα : 1 < α ∧ α < 2) (ρ : Matrix (S × Q) (S × Q) ℂ) (hρ : Density ρ)
    (ω : Matrix S S ℂ) (hω : ω.PosDef) :
    divergence α ρ (Matrix.kronecker ω (rightMarginal ρ)) ≤
      ⨅ σ : {σ : Matrix Q Q ℂ // Density σ},
        divergence (1 / (2 - α)) ρ (Matrix.kronecker ω σ.1) := by sorry

end FlexRigidity
