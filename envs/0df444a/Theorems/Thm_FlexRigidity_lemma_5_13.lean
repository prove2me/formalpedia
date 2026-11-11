-- Prove2me | Theorems.Thm_FlexRigidity_lemma_5_13
-- name    : FlexRigidity.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:34:53.48132+00:00
-- url     : https://prove2.me/theorems/69bb2062-9b07-420f-82c6-9b70e9615225
-- title:
--   Lemma 5.13 — reduction to the DD protocol
-- statement:
--   Under Postulate Sets 5.4 and 5.1, let $\rho^{\mathrm{ideal}}=\mathcal F^\mu_n\circ\cdots\circ\mathcal F^\mu_1[\rho^0]$ be the output of the §5.3 ideal channels on a normalized $\rho^0_{M^{\mathrm A}_1M^{\mathrm B}_1R}$, and let $\mathcal M$ be the final channel of §5.6: if fewer than $m$ rounds are generation rounds it outputs $0$; otherwise it keeps $(x_E,a_E)$ for the first $m$ generation rounds $E$ and Bob's memory, side information and transcript, and runs the DD continuation with the fixed attack. Then
--   $$\Pr_{\mathcal M[\rho^{\mathrm{ideal}}]}[\mathrm{Bad}]\le q_{\mathrm{dep}}(\mu)^m,$$
--   with $m=\lfloor(1-\gamma)n/2\rfloor$ and the same $\mu$ in the ideal channels and in Postulate 5.1. The ideal process is not conditioned on acceptance.
--
--   Differences from the source:
--   - generalization: the isometries V^A_i, V^B_i chosen from Postulate 5.3(iii) for the families of (47), with recovery channels N^A_i, N^B_i → any isometries satisfying the self-testing bound (41) for the round's families and any CPTP left inverses (Extraction.IsAdmissible); reason: Postulate 5.3(iii) is used only through these properties of the chosen maps; the paper's choice is one admissible choice, so the Lean statement specializes to it
--   - encoding: devices in the stored-output form (47) with ancillas M′^A_i, M′^B_i in |0⟩ → StoredImpl: ancilla Fin (k+1) with |0⟩ the basis vector 0, memories Fin d; reason: Lean convention; every finite ancilla with a fixed |0⟩ is of this form up to relabelling
--   - generalization: a DD protocol P_m of the form of Protocol 1 and its allowed attacks → any abstract experiment (attack types Att m d, effects Bad_κ) satisfying Postulate 5.1; reason: Postulate 5.1 is all the lemma uses; every Protocol-1 protocol induces such an experiment
--   - generalization: pure |ψ_{x,a}⟩ with the realization (39) → ρ^{prep,µ} defined from (P_X, |ϕ⟩, {T^x_a}); reason: by (39) it equals (36)
--   - reading: "for every relevant 0 < µ < 1" in Postulate 5.1 → Postulate 5.1 on (0, µbar) and µ ∈ (0, µbar); reason: fewer assumed µ is the stronger lemma
--   - encoding: T_i of (49), given on the inputs G_i produces (generation triples with the generation summand of J_i, test triples with the test summand) → roundT, which processes the two never-occurring sectors by the same two branch maps and pinches Z_i, A_i on the generation branch; reason: G_i never outputs into those sectors, so E_i = T_i ∘ G_i and F_i = T_i ∘ P_i ∘ G_i are unchanged; the extension makes T_i a channel, as Postulate 4.1 requires
--   - encoding: P_i of the form (16), specified on Z_i-classical inputs → ctrlReplacer, which pinches Z_i first and then acts as (16); reason: G_i has classical output Z_i, so P_i ∘ G_i and F_i are unchanged
--   - reading: M retains Bob's memory and his classical transcript; R is external side information → the DD continuation acts on M^B_{n+1}, R and Bob's transcript (u_i, y_i, b_i); reason: the proof of Lemma 5.13 (p. 56) keeps R with Bob (R_i = R X_{E∩[i−1]} …); the stronger reading: the attack may use R
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 5.13, §5.6, p. 56

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_diSeqData
import Definitions.Def_FlexRigidity_seqRun
import Definitions.Def_FlexRigidity_finalOp
import Definitions.Def_FlexRigidity_Postulate51
import Definitions.Def_FlexRigidity_prepState
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 5.13 (Reduction to the DD protocol)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 56). Under Postulate Sets 5.4 and 5.1, the channel
`M` defined in §5.6 satisfies `Pr_{M[ρ^ideal]}[Bad] ≤ (q_dep(µ))^m`.

**Formalization Note** `ρ^ideal = F_n ∘ ⋯ ∘ F_1[ρ⁰]` with the §5.3 ideal channels
`F^µ_i = T_i ∘ P_i ∘ G_i` (`diSeqData`), for devices in stored-output form and any admissible
extraction data, and any normalized `ρ⁰_{M^A_1M^B_1R}` (`R = Fin r`); `m = ⌊(1−γ)n/2⌋`. `M` is
`finalOp` with no acceptance check, followed by the DD continuation attack `κ`, so
`Pr_{M[ρ^ideal]}[Bad] = Tr[Bad_κ · finalOp(ρ^ideal)]`. The same `µ ∈ (0, µbar)` defines the ideal
channels and is used in Postulate 5.1; `0 < µ < 1` as in (36). -/
theorem lemma_5_13 {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype SA] [Fintype SB] [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq SA] [DecidableEq SB]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (van : ℝ → ℝ)
    (hG : G.IsValid) (hRz : Rz.IsPostulate53ii G)
    (I : StoredImpl X Y A B) (n : ℕ) (hI : I.IsValid n) (Ex : Extraction X Y A B SA SB I)
    (hEx : Ex.IsAdmissible G Rz van n) (DD : DDExperiment X A) (hDD : DD.IsValid)
    (qdep : ℝ → ℝ) (μbar : ℝ) (h51 : Postulate51 DD (prepState Rz) qdep μbar)
    (γ μ : ℝ) (hγ : 0 < γ ∧ γ < 1) (hμ : 0 < μ ∧ μ < μbar) (hμ1 : μ < 1) (r : ℕ)
    (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ)
    (hρ0 : Density ρ0)
    (κ : DD.Att ⌊(1 - γ) * n / 2⌋₊
      (Fintype.card ((Fin n → Bool × Option Y × Option B) × (Fin r × Fin (I.dB n))))) :
    tr (DD.Bad _ _ κ * finalOp ⌊(1 - γ) * n / 2⌋₊ (fun _ => True)
        (seqRun (diSeqData G Rz γ μ Ex).F ρ0 n)) ≤ qdep μ ^ ⌊(1 - γ) * n / 2⌋₊ := by sorry

end FlexRigidity
