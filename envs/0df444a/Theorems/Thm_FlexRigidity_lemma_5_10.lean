-- Prove2me | Theorems.Thm_FlexRigidity_lemma_5_10
-- name    : FlexRigidity.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:43.091647+00:00
-- url     : https://prove2.me/theorems/faf7cd67-aa21-4161-9f6c-04f8e3effb48
-- title:
--   Lemma 5.10 — direct-sum comparison exponent
-- statement:
--   For the §5.3 channels $\mathcal G_i$, $\mathcal P_i$ and $\alpha>1$,
--   $$\mathrm{CompExp}_\alpha(\mathcal G,\mathcal P\circ\mathcal G;S_{\mathrm{Acc}})\le n\sup_{\substack{\sigma^\oplus\\\bar Q_C\in S_{\mathrm{Acc}}}}\Big[\bar Q_C(\mathrm{gen})D_\alpha\big(\sigma^{\oplus,\mathcal G}_{|\mathrm{gen}}\big\|\sigma^{\oplus,\mathcal P\circ\mathcal G}_{|\mathrm{gen}}\big)-\frac1{\alpha-1}D(\bar Q_C\|\bar P_C)\Big],$$
--   where $\sigma^\oplus$ ranges over states $\frac1n\sum_i|i\rangle\langle i|\otimes|\sigma^i\rangle\langle\sigma^i|$, $\sigma^{\oplus,\mathcal G}$ and $\sigma^{\oplus,\mathcal P\circ\mathcal G}$ are the outputs of the direct-sum channels, and $\bar P_C=\frac1n\sum_iP_{C_i}$ is their record distribution. It reduces the $n$-round optimization to a single-round one.
--
--   **Formalization Note** $S_{\mathrm{Acc}}$ is (42) for the protocol parameters $\gamma,\mu\in(0,1)$, $0<\varepsilon_{\mathrm{tol}}\le(1-\gamma)/2$; $\cdot_{|\mathrm{gen}}$ is the normalized $C=\mathrm{gen}$ block.
--
--   Differences from the source:
--   - generalization: the isometries V^A_i, V^B_i chosen from Postulate 5.3(iii) for the families of (47), with recovery channels N^A_i, N^B_i → any isometries satisfying the self-testing bound (41) for the round's families and any CPTP left inverses (Extraction.IsAdmissible); reason: Postulate 5.3(iii) is used only through these properties of the chosen maps; the paper's choice is one admissible choice, so the Lean statement specializes to it
--   - encoding: devices in the stored-output form (47) with ancillas M′^A_i, M′^B_i in |0⟩ → StoredImpl: ancilla Fin (k+1) with |0⟩ the basis vector 0, memories Fin d; reason: Lean convention; every finite ancilla with a fixed |0⟩ is of this form up to relabelling
--   - encoding: the references R_i embedded in one common register R → each summand of σ⊕ keeps its own reference R_i ≅ M_i; reason: an isometric embedding changes no divergence or distribution
--   - encoding: T_i of (49), given on the inputs G_i produces (generation triples with the generation summand of J_i, test triples with the test summand) → roundT, which processes the two never-occurring sectors by the same two branch maps and pinches Z_i, A_i on the generation branch; reason: G_i never outputs into those sectors, so E_i = T_i ∘ G_i and F_i = T_i ∘ P_i ∘ G_i are unchanged; the extension makes T_i a channel, as Postulate 4.1 requires
--   - encoding: P_i of the form (16), specified on Z_i-classical inputs → ctrlReplacer, which pinches Z_i first and then acts as (16); reason: G_i has classical output Z_i, so P_i ∘ G_i and F_i are unchanged
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 5.10, pp. 51–52

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_diSeqData
import Definitions.Def_FlexRigidity_compExp
import Definitions.Def_FlexRigidity_SAcc
import Definitions.Def_FlexRigidity_dsOut
import Definitions.Def_FlexRigidity_klDiv
import Definitions.Def_DHRUniq_IsUnitVec
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

open Classical in
/-- **Lemma 5.10 (Direct-sum comparison exponent)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, pp. 51–52). For `α > 1` and `σ⊕, σ⊕,G, σ⊕,P∘G, P̄_C, Q̄_C`
as defined on p. 51,
`CompExp_α(G, P∘G; S_Acc) ≤ n sup_{σ⊕, Q̄_C ∈ S_Acc} [ Q̄_C(gen) D_α(σ⊕,G_{|gen}‖σ⊕,P∘G_{|gen}) − (1/(α−1)) D(Q̄_C‖P̄_C) ]`,
where the optimization over `σ⊕` is over states of the form `(1/n) Σ_i |i⟩⟨i| ⊗ |σ^i⟩⟨σ^i|`.

**Formalization Note** `G_i`, `P_i` are the §5.3 channels (`diSeqData`) for any admissible
extraction data; `P̄_C = (1/n) Σ_i P_{C_i}` is the record distribution of `σ⊕,G` (not the protocol's
ideal distribution `P_C`), while `S_Acc` is (42). `·_{|gen}` is the normalized `C = gen` block. -/
theorem lemma_5_10 {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype SA] [Fintype SB] [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq SA] [DecidableEq SB]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (van : ℝ → ℝ)
    (hG : G.IsValid) (hRz : Rz.IsPostulate53ii G)
    (I : StoredImpl X Y A B) (n : ℕ) (hI : I.IsValid n) (Ex : Extraction X Y A B SA SB I)
    (hEx : Ex.IsAdmissible G Rz van n) (γ μ εtol : ℝ) (hγ : 0 < γ ∧ γ < 1) (hμ : 0 < μ ∧ μ < 1)
    (hε : 0 < εtol ∧ εtol ≤ (1 - γ) / 2) (α : ℝ) (hα : 1 < α) :
    let D := diSeqData G Rz γ μ Ex
    let SA' := SAcc γ (quantumValue G) εtol
    let cut : Option Bool →
        Matrix (Σ i : Fin n, (Fin (I.dA i) × Fin (I.dB i)) × ((Bool × X × Option Bool) × (A × SA × SB) ×
          RoundJ Y B (Ex.qA i) (Ex.qB i) (I.dA (i + 1)) (I.dB (i + 1))))
          (Σ i : Fin n, (Fin (I.dA i) × Fin (I.dB i)) × ((Bool × X × Option Bool) × (A × SA × SB) ×
          RoundJ Y B (Ex.qA i) (Ex.qB i) (I.dA (i + 1)) (I.dB (i + 1)))) ℂ →
        Matrix (Σ i : Fin n, (Fin (I.dA i) × Fin (I.dB i)) × ((Bool × X × Option Bool) × (A × SA × SB) ×
          RoundJ Y B (Ex.qA i) (Ex.qB i) (I.dA (i + 1)) (I.dB (i + 1))))
          (Σ i : Fin n, (Fin (I.dA i) × Fin (I.dB i)) × ((Bool × X × Option Bool) × (A × SA × SB) ×
          RoundJ Y B (Ex.qA i) (Ex.qB i) (I.dA (i + 1)) (I.dB (i + 1)))) ℂ :=
      fun c Xm => Matrix.of fun p q => if p.2.2.1.2.2 = c ∧ q.2.2.1.2.2 = c then Xm p q else 0
    compExp D n α SA' ≤ (n : EReal) * sSup {v : EReal |
      ∃ σ : (i : Fin n) → ((Fin (I.dA i) × Fin (I.dB i)) × (Fin (I.dA i) × Fin (I.dB i)) → ℂ),
        (∀ i, DHRUniq.IsUnitVec (σ i)) ∧ ∃ Q ∈ SA',
          let σG := dsOut n D.G σ
          let σPG := dsOut n (fun k X => D.P k (D.G k X)) σ
          let pg := tr (cut none σG)
          v = (Q none : EReal) * divergence α (((pg⁻¹ : ℝ) : ℂ) • cut none σG)
                (((pg⁻¹ : ℝ) : ℂ) • cut none σPG) -
              ((1 / (α - 1) : ℝ) : EReal) * klDiv Q (fun c => tr (cut c σG))} := by sorry

end FlexRigidity
