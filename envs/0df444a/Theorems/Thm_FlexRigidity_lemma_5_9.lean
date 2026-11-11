-- Prove2me | Theorems.Thm_FlexRigidity_lemma_5_9
-- name    : FlexRigidity.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:57.19668+00:00
-- url     : https://prove2.me/theorems/0759f31d-20d1-465b-8d9f-988315f52b98
-- title:
--   Lemma 5.9 — divergence after averaging the input
-- statement:
--   Under the assumptions of Lemma 5.8 and $0<\mu<1$, with $|S|=|A||S_{\mathrm A}||S_{\mathrm B}|$, the CQ states $\zeta$ and $\tilde\omega^\mu$ of (57) satisfy
--   $$\zeta_{X_iS_iRQ^{\mathrm A}_iQ^{\mathrm B}_i}\le\frac{|S|^2}{\mu}\tilde\omega^\mu_{X_iS_iRQ^{\mathrm A}_iQ^{\mathrm B}_i},$$
--   and for every $\alpha>1$
--   $$D_\alpha\big(\zeta\big\|\tilde\omega^\mu\big)\le\log a_\mu^{-1}+\mathrm{van}_{\mu,\mathsf G,\alpha}(\delta).$$
--   For every fixed $\mu\in(0,1)$ and $\alpha>1$, the function $\mathrm{van}_{\mu,\mathsf G,\alpha}$ of (53) is vanishing.
--
--   **Formalization Note** "Vanishing" is Definition 2.2 on $[0,\omega^*]$, the range of the deficit, given that $\mathrm{van}_{\mathsf G}$ is vanishing there (Postulate 5.3(iii)).
--
--   Differences from the source:
--   - generalization: the isometries V^A_i, V^B_i chosen from Postulate 5.3(iii) for the families of (47), with recovery channels N^A_i, N^B_i → any isometries satisfying the self-testing bound (41) for the round's families and any CPTP left inverses (Extraction.IsAdmissible); reason: Postulate 5.3(iii) is used only through these properties of the chosen maps; the paper's choice is one admissible choice, so the Lean statement specializes to it
--   - encoding: devices in the stored-output form (47) with ancillas M′^A_i, M′^B_i in |0⟩ → StoredImpl: ancilla Fin (k+1) with |0⟩ the basis vector 0, memories Fin d; reason: Lean convention; every finite ancilla with a fixed |0⟩ is of this form up to relabelling
--   - reading: van_{µ,G,α} "is vanishing" (Definition 2.2 on [0, a], a unspecified) → IsVanishing on [0, ω*]; reason: δ is a deficit, which lies in [0, ω*]
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 5.9, eqs. (53), (56)–(57), pp. 47–49

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_zetaCQ
import Definitions.Def_FlexRigidity_omegaTildeCQ
import Definitions.Def_FlexRigidity_vanMuGA
import Definitions.Def_FlexRigidity_roundDeficit
import Definitions.Def_FlexRigidity_IsVanishing
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 5.9 (Divergence after averaging the input)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 49). For every `α > 1`, the states defined in (57)
satisfy `ζ_{X_iS_iRQ^A_iQ^B_i} ≤ (|S|²/µ) ω̃^µ_{X_iS_iRQ^A_iQ^B_i}` and
`D_α(ζ_{X_iS_iRQ^A_iQ^B_i}‖ω̃^µ_{X_iS_iRQ^A_iQ^B_i}) ≤ log a_µ^{−1} + van_{µ,G,α}(δ)`.
For every fixed `µ ∈ (0, 1)` and `α > 1`, the function `van_{µ,G,α}` defined in (53) is vanishing.

**Formalization Note** Standing assumptions of §5.4 as in Lemma 5.8, with `0 < µ < 1` and
`|S| = |A||S_A||S_B|`; "vanishing" is Definition 2.2 on `[0, ω*]`, the range of the deficit, with
`van_G` vanishing there (Postulate 5.3(iii)). The operator inequality is
`(|S|²/µ) ω̃^µ − ζ ⪰ 0`. -/
theorem lemma_5_9 {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype SA] [Fintype SB] [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq SA] [DecidableEq SB]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (van : ℝ → ℝ)
    (hG : G.IsValid) (hRz : Rz.IsPostulate53ii G) (hvan : IsVanishing van (quantumValue G))
    (I : StoredImpl X Y A B) (n : ℕ) (hI : I.IsValid n) (Ex : Extraction X Y A B SA SB I)
    (hEx : Ex.IsAdmissible G Rz van n) (i : ℕ) (hi : i < n) (r : ℕ)
    (ρ : Fin r × (Fin (I.dA i) × Fin (I.dB i)) → ℂ) (hρ : DHRUniq.IsUnitVec ρ) (μ : ℝ)
    (hμ : 0 < μ ∧ μ < 1) :
    let s := Fintype.card (A × SA × SB)
    let δ := roundDeficit G I i ρ
    let ζ := zetaCQ Rz Ex i ρ
    let ω := omegaTildeCQ Rz Ex i ρ μ
    ((((s : ℝ) ^ 2 / μ : ℝ) : ℂ) • ω - ζ).PosSemidef ∧
    (∀ α : ℝ, 1 < α → divergence α ζ ω ≤
      ((Real.logb 2 (1 / aMu μ s) + vanMuGA van s μ α δ : ℝ) : EReal)) ∧
    ∀ μ' α : ℝ, 0 < μ' → μ' < 1 → 1 < α → IsVanishing (vanMuGA van s μ' α) (quantumValue G) := by sorry

end FlexRigidity
