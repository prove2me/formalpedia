-- Prove2me | Theorems.Thm_FlexRigidity_theorem_5_12
-- name    : FlexRigidity.theorem_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:34:56.848274+00:00
-- url     : https://prove2.me/theorems/117b34dd-8b94-49e0-884e-960f7a6e56c5
-- title:
--   Theorem 5.12 — $\mathrm{CompExp}_{1/(2-\alpha)}\le n\cdot\mathrm{cost}_{\alpha,\mu}(\gamma,\varepsilon_{\mathrm{tol}})$
-- statement:
--   Assume Postulate Sets 5.3 and 5.4. For every $1<\alpha<2$, $\mu\in(0,1)$, $\gamma\in(0,1)$ and $0<\varepsilon_{\mathrm{tol}}\le(1-\gamma)/2$, the §5.3 channels satisfy
--   $$\mathrm{CompExp}_{1/(2-\alpha)}(\mathcal G,\mathcal P\circ\mathcal G;S_{\mathrm{Acc}_{\varepsilon_{\mathrm{tol}}}})\le n\cdot\mathrm{cost}_{\alpha,\mu}(\gamma,\varepsilon_{\mathrm{tol}}),$$
--   with the cost function (66). Combined with Theorem 4.4 it bounds the divergence between the accepted real state and the ideal state linearly in $n$.
--
--   Differences from the source:
--   - generalization: the isometries V^A_i, V^B_i chosen from Postulate 5.3(iii) for the families of (47), with recovery channels N^A_i, N^B_i → any isometries satisfying the self-testing bound (41) for the round's families and any CPTP left inverses (Extraction.IsAdmissible); reason: Postulate 5.3(iii) is used only through these properties of the chosen maps; the paper's choice is one admissible choice, so the Lean statement specializes to it
--   - encoding: devices in the stored-output form (47) with ancillas M′^A_i, M′^B_i in |0⟩ → StoredImpl: ancilla Fin (k+1) with |0⟩ the basis vector 0, memories Fin d; reason: Lean convention; every finite ancilla with a fixed |0⟩ is of this form up to relabelling
--   - generalization: Postulate Set 5.3(iii) (van_G vanishing and the isometries of every family) → van_G vanishing on [0, ω*] and admissible extraction data for the rounds used; reason: the proof uses 5.3(iii) only through these; they follow from it
--   - encoding: T_i of (49), given on the inputs G_i produces (generation triples with the generation summand of J_i, test triples with the test summand) → roundT, which processes the two never-occurring sectors by the same two branch maps and pinches Z_i, A_i on the generation branch; reason: G_i never outputs into those sectors, so E_i = T_i ∘ G_i and F_i = T_i ∘ P_i ∘ G_i are unchanged; the extension makes T_i a channel, as Postulate 4.1 requires
--   - encoding: P_i of the form (16), specified on Z_i-classical inputs → ctrlReplacer, which pinches Z_i first and then acts as (16); reason: G_i has classical output Z_i, so P_i ∘ G_i and F_i are unchanged
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Theorem 5.12, p. 55

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_diSeqData
import Definitions.Def_FlexRigidity_compExp
import Definitions.Def_FlexRigidity_SAcc
import Definitions.Def_FlexRigidity_cost
import Definitions.Def_FlexRigidity_IsVanishing
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Theorem 5.12 (Comparison bound for optimizing soundness)** (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 55). Assume Postulate Sets 5.3 and 5.4.
For every `1 < α < 2`, `µ ∈ (0, 1)`, `γ ∈ (0, 1)` and `0 < ε_tol ≤ (1−γ)/2`,
`CompExp_{1/(2−α)}(G, P∘G; S_{Acc_εtol}) ≤ n · cost_{α,µ}(γ, ε_tol)`.

**Formalization Note** `G_i`, `P_i` are the §5.3 channels (`diSeqData`) for devices in stored-output
form (47) and any admissible extraction data; `van_G` is vanishing on `[0, ω*]`; `cost` uses
`ω*`, `|S| = |A||S_A||S_B|` and `van_G`. -/
theorem theorem_5_12 {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype SA] [Fintype SB] [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq SA] [DecidableEq SB]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (van : ℝ → ℝ)
    (hG : G.IsValid) (hRz : Rz.IsPostulate53ii G) (hvan : IsVanishing van (quantumValue G))
    (I : StoredImpl X Y A B) (n : ℕ) (hI : I.IsValid n) (Ex : Extraction X Y A B SA SB I)
    (hEx : Ex.IsAdmissible G Rz van n) (α μ γ εtol : ℝ) (hα : 1 < α ∧ α < 2)
    (hμ : 0 < μ ∧ μ < 1) (hγ : 0 < γ ∧ γ < 1) (hε : 0 < εtol ∧ εtol ≤ (1 - γ) / 2) :
    compExp (diSeqData G Rz γ μ Ex) n (1 / (2 - α)) (SAcc γ (quantumValue G) εtol) ≤
      (n : EReal) * cost van (quantumValue G) (Fintype.card (A × SA × SB)) α μ γ εtol := by sorry

end FlexRigidity
