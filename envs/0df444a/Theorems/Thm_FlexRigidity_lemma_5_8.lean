-- Prove2me | Theorems.Thm_FlexRigidity_lemma_5_8
-- name    : FlexRigidity.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:21.716347+00:00
-- url     : https://prove2.me/theorems/48bed35d-f165-4fd7-b6a6-479034b8e88d
-- title:
--   Lemma 5.8 — self-testing of the coherent state
-- statement:
--   Assume Postulate Sets 5.3 and 5.4, devices in the stored-output form (47), and extraction isometries $V^{\mathrm A}_i,V^{\mathrm B}_i$ satisfying the self-testing bound (41) for the round's projector families. For a normalized purified input $|\rho\rangle_{RM^{\mathrm A}_iM^{\mathrm B}_i}$ with round-strategy deficit $\delta$, and the vectors $|\phi^x\rangle$, $|\zeta^x\rangle$ and errors $\eta_x$ of (54)–(55), there is a normalized $|\tau_\rho\rangle_Q$, $Q=RQ^{\mathrm A}_iQ^{\mathrm B}_i$, with
--   $$\sum_xP_X(x)\big\||\zeta_x\rangle-|\phi_x\rangle|\tau_\rho\rangle\big\|_2^2\le\mathrm{van}_{\mathsf G}(\delta)^2,$$
--   and consequently $\sum_xP_X(x)\eta_x\le\mathrm{van}_{\mathsf G}(\delta)^2$. It feeds the single-round bound Lemma 5.9.
--
--   Differences from the source:
--   - generalization: the isometries V^A_i, V^B_i chosen from Postulate 5.3(iii) for the families of (47), with recovery channels N^A_i, N^B_i → any isometries satisfying the self-testing bound (41) for the round's families and any CPTP left inverses (Extraction.IsAdmissible); reason: Postulate 5.3(iii) is used only through these properties of the chosen maps; the paper's choice is one admissible choice, so the Lean statement specializes to it
--   - encoding: devices in the stored-output form (47) with ancillas M′^A_i, M′^B_i in |0⟩ → StoredImpl: ancilla Fin (k+1) with |0⟩ the basis vector 0, memories Fin d; reason: Lean convention; every finite ancilla with a fixed |0⟩ is of this form up to relabelling
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 5.8, eqs. (54)–(55), p. 48

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_etaX
import Definitions.Def_FlexRigidity_roundDeficit
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 5.8 (Self-testing of the coherent state)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 48). With `van_G` as in (41), and the states and
`η_{x_i}` defined in (54) and (55), there is a normalized vector `|τ_ρ⟩_Q` such that
`Σ_{x_i} P_X(x_i) ‖|ζ^{x_i}⟩ − |ϕ^{x_i}⟩|τ_ρ⟩‖²₂ ≤ van_G(δ)²`. Consequently,
`Σ_{x_i} P_X(x_i) η_{x_i} ≤ van_G(δ)²`.

**Formalization Note** Standing assumptions of §5.4: Postulate Sets 5.3 and 5.4, devices in the
stored-output form (47), and extraction isometries `V^A_i, V^B_i` satisfying (41) for the round's
projector families (any admissible choice). `|ρ⟩` is any normalized purified input on
`R M^A_i M^B_i` with `R = Fin r`; `Q = R Q^A_i Q^B_i`; `δ` is the deficit of the round strategy. -/
theorem lemma_5_8 {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype SA] [Fintype SB] [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq SA] [DecidableEq SB]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (van : ℝ → ℝ)
    (hG : G.IsValid) (hRz : Rz.IsPostulate53ii G) (I : StoredImpl X Y A B) (n : ℕ)
    (hI : I.IsValid n) (Ex : Extraction X Y A B SA SB I) (hEx : Ex.IsAdmissible G Rz van n)
    (i : ℕ) (hi : i < n) (r : ℕ) (ρ : Fin r × (Fin (I.dA i) × Fin (I.dB i)) → ℂ)
    (hρ : DHRUniq.IsUnitVec ρ) :
    let δ := roundDeficit G I i ρ
    (∃ τ : Fin r × (Fin (Ex.qA i) × Fin (Ex.qB i)) → ℂ, DHRUniq.IsUnitVec τ ∧
      ∑ x, Rz.PX x * ∑ p : (A × SA × SB) × (Fin r × (Fin (Ex.qA i) × Fin (Ex.qB i))),
        ‖zetaX Ex i ρ x p - phiX Rz x p.1 * τ p.2‖ ^ 2 ≤ van δ ^ 2) ∧
    ∑ x, Rz.PX x * etaX Rz Ex i ρ x ≤ van δ ^ 2 := by sorry

end FlexRigidity
