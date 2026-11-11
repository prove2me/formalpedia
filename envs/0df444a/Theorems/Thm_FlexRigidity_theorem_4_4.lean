-- Prove2me | Theorems.Thm_FlexRigidity_theorem_4_4
-- name    : FlexRigidity.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:21:48.209163+00:00
-- url     : https://prove2.me/theorems/44c45a10-6814-4d9a-bb62-590e9f726ca0
-- title:
--   Theorem 4.4 — sequential testing comparison
-- statement:
--   Assume Postulate Set 4.1: round channels $\mathcal E_i=\mathcal T_i\circ\mathcal G_i$, $\mathcal F_i=\mathcal T_i\circ\mathcal P_i\circ\mathcal G_i$ with classical records $C_i$, and an accept set $S_\Omega$ (nonempty, closed, convex) defining $\Omega=\{\mathrm{freq}_{\mathbf c}\in S_\Omega\}$. Fix a normalized initial state $\rho^0_{M_1R}$, $R$ external side information untouched by all channels, and let $\rho^{\mathrm{real}}=\mathcal E_n\circ\cdots\circ\mathcal E_1[\rho^0]$, $\rho^{\mathrm{ideal}}=\mathcal F_n\circ\cdots\circ\mathcal F_1[\rho^0]$, $p_\Omega=\Pr_{\rho^{\mathrm{real}}}[\Omega]$. If $1<\alpha<2$ and $p_\Omega>0$, then
--   $$D_\alpha\big(\rho^{\mathrm{real}}_{|\Omega}\big\|\rho^{\mathrm{ideal}}\big)\le\mathrm{CompExp}_{1/(2-\alpha)}(\mathcal G,\mathcal P\circ\mathcal G;S_\Omega)+\frac{\alpha}{\alpha-1}\log\frac1{p_\Omega},$$
--   and for every $0<\varepsilon<1$,
--   $$D^\varepsilon_{\max}\big(\rho^{\mathrm{real}}_{|\Omega}\big\|\rho^{\mathrm{ideal}}\big)\le\mathrm{CompExp}_{1/(2-\alpha)}(\mathcal G,\mathcal P\circ\mathcal G;S_\Omega)+\frac{\log(1/\varepsilon^2)+\alpha\log(1/p_\Omega)}{\alpha-1}.$$
--   This is the paper's sequential comparison theorem, the engine of the soundness proof of Theorem 5.6.
--
--   Differences from the source:
--   - reading: T_i "only uses C_i as a control register" (Postulate 4.1(i)) → T_i maps every operator supported on the block C_i = c to an operator supported on the output block C_i = c; reason: the property the proof uses (p. 29, "Since T_i preserves C_i")
--   - encoding: P_i of the form (16) on Z_i-classical inputs → ctrlReplacer, which pinches Z_i first; reason: G_i has classical output Z_i, so F_i is unchanged
--   - encoding: rounds i = 1, …, n with registers of varying dimension → families indexed by all i ∈ ℕ (Lean rounds 0, …, n−1), of which the statement uses the first n; registers are finite types; reason: Lean convention; data for later rounds are never used, and every finite family extends
--   - encoding: R_i with |R_i| ≥ |M_i| in (19) → R_i ≅ M_i; reason: by Lemma 4.3(i) the value does not depend on the choice
--   - encoding: divergences and channel divergences with values in [0, +∞] → values in EReal (extended reals); reason: Lean convention; the +∞ conventions of Definition 2.7 are kept, no instance changes
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Theorem 4.4, pp. 33–34

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_compExp
import Definitions.Def_FlexRigidity_seqRun
import Definitions.Def_FlexRigidity_IsAcceptSet
import Definitions.Def_FlexRigidity_condEvent
import Definitions.Def_FlexRigidity_freq
import Definitions.Def_FlexRigidity_smoothMaxDiv
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

open Classical in
/-- **Theorem 4.4 (Sequential testing comparison)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, pp. 33–34). Fix a normalized initial state
`ρ⁰_{M_1R}` (`R` arbitrary external side information, untouched by all channels), set
`ρ^real = E[ρ⁰]`, `ρ^ideal = F[ρ⁰]` and `p_Ω = Pr_{ρ^real}[Ω]`. Under Postulate Set 4.1, let
`1 < α < 2` and `p_Ω > 0`. Then
`D_α(ρ^real_{|Ω}‖ρ^ideal) ≤ CompExp_{1/(2−α)}(G, P∘G; S_Ω) + (α/(α−1)) log(1/p_Ω)`.
Consequently, for every `0 < ε < 1`,
`D^ε_max(ρ^real_{|Ω}‖ρ^ideal) ≤ CompExp_{1/(2−α)}(G, P∘G; S_Ω) + (log(1/ε²) + α log(1/p_Ω))/(α−1)`.

**Formalization Note** `Ω = {freq_c ∈ S_Ω}` is an event on the record string read from the
protected registers; `ρ_{|Ω}` is `condEvent`. Logs base 2; values in `EReal`. -/
theorem theorem_4_4 {C : Type} {O M Z S J : ℕ → Type} [Fintype C] [DecidableEq C]
    [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
    [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)] [∀ k, Fintype (Z k)] [∀ k, DecidableEq (Z k)]
    [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)] [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (D : SeqData C O M Z S J) (n : ℕ) (hD : D.IsPostulate41 n) (SΩ : Set (C → ℝ))
    (hS : IsAcceptSet SΩ) {R : Type} [Fintype R] [DecidableEq R]
    (ρ0 : Matrix (R × M 0) (R × M 0) ℂ) (hρ0 : Density ρ0) (α : ℝ) (hα : 1 < α ∧ α < 2) :
    let Ω : Hist C O n → Prop := fun h => freq (Hist.cs n h) ∈ SΩ
    let ρreal := seqRun D.E ρ0 n
    let ρideal := seqRun D.F ρ0 n
    let pΩ := tr (cutEvent Ω ρreal)
    0 < pΩ →
    divergence α (condEvent Ω ρreal) ρideal ≤
        compExp D n (1 / (2 - α)) SΩ + (((α / (α - 1)) * Real.logb 2 (1 / pΩ) : ℝ) : EReal) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      smoothMaxDiv ε (condEvent Ω ρreal) ρideal ≤ compExp D n (1 / (2 - α)) SΩ +
        (((Real.logb 2 (1 / ε ^ 2) + α * Real.logb 2 (1 / pΩ)) / (α - 1) : ℝ) : EReal) := by sorry

end FlexRigidity
