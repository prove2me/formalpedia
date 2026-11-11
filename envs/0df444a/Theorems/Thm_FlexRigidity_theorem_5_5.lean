-- Prove2me | Theorems.Thm_FlexRigidity_theorem_5_5
-- name    : FlexRigidity.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:25:02.216336+00:00
-- url     : https://prove2.me/theorems/f9f48b0a-869d-41da-a6a7-9af44c837e4c
-- title:
--   Theorem 5.5 — completeness, and $E$ is well defined on acceptance
-- statement:
--   In Protocol 2 (testing probability $\gamma\in(0,1)$, tolerance $0<\varepsilon_{\mathrm{tol}}\le(1-\gamma)/2$, $m=\lfloor(1-\gamma)n/2\rfloor$), suppose the honest rounds are independent and in every round the devices use the same strategy $\mathfrak S$ with deficit $\delta_{\mathsf G}(\mathfrak S)=\delta_{\mathrm{hon}}$. If $\gamma\delta_{\mathrm{hon}}<\varepsilon_{\mathrm{tol}}$, then
--   $$\Pr_{\mathcal P'}\big[\|\mathrm{freq}_{\mathbf c}-P_C\|_{\mathrm{tr}}>\varepsilon_{\mathrm{tol}}\big]\le2|C|\exp\Big(-\frac{8n(\varepsilon_{\mathrm{tol}}-\gamma\delta_{\mathrm{hon}})^2}{|C|^2}\Big)=6\exp\Big(-\frac{8n(\varepsilon_{\mathrm{tol}}-\gamma\delta_{\mathrm{hon}})^2}{9}\Big).$$
--   On every accepting execution, the set $E$ of Protocol 2 is well defined and has size $m$. The second claim is used in the proof of Theorem 5.6.
--
--   **Formalization Note** The honest record distribution is the product over the $n$ rounds of the single-round law (`honestRecordProb`), with $P_X$ the game's $X$-marginal. The second claim is the deterministic statement that every record string $\mathbf c$ with $\|\mathrm{freq}_{\mathbf c}-P_C\|_{\mathrm{tr}}\le\varepsilon_{\mathrm{tol}}$ contains at least $m$ entries $\mathrm{gen}$, for every $n$.
--
--   Differences from the source:
--   - reading: "the honest rounds are independent and in every round the devices use the same strategy S" → the n round records are i.i.d. with the single-round law honestRecordProb of S (P_X the game's X-marginal); reason: only the records enter (43)
--   - reading: "On every accepting execution, E is well defined and has size m" → every record string c with ‖freq_c − P_C‖_tr ≤ ε_tol has at least m entries gen; reason: E is the first m generation rounds; it exists iff there are at least m of them
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Theorem 5.5, eq. (43), p. 42

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_honestRecordProb
import Definitions.Def_FlexRigidity_deficit
import Definitions.Def_FlexRigidity_recordOf
import Definitions.Def_FlexRigidity_PC
import Definitions.Def_HybridXorLift_tvDist
import Definitions.Def_FlexRigidity_freq
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Theorem 5.5 (Completeness)** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, p. 42). Suppose the honest rounds are independent and in every round the
devices use the same strategy `S` with deficit `δ_G(S) = δ_hon`. If `γ δ_hon < ε_tol`, then
`Pr_{P′}[‖freq_c − P_C‖_tr > ε_tol] ≤ 2|C| exp(−8n(ε_tol − γδ_hon)²/|C|²) = 6 exp(−8n(ε_tol − γδ_hon)²/9)` (43).
On every accepting execution, the set `E` in Protocol 2 is well defined and has size `m`.

**Formalization Note** Protocol 2's parameters: `γ ∈ (0, 1)`, `0 < ε_tol ≤ (1−γ)/2`,
`m = ⌊(1−γ)n/2⌋`. Independent honest rounds with strategy `S` give the product distribution of
`honestRecordProb` over the `n` round records; `|C| = 3`. The second claim is the deterministic
statement that every record string `c` with `‖freq_c − P_C‖_tr ≤ ε_tol` has at least `m` entries
`gen`, for every `n`. -/
theorem theorem_5_5 {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (hG : G.IsValid) {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (H : X → A → Matrix (Fin dA) (Fin dA) ℂ)
    (K : Y → B → Matrix (Fin dB) (Fin dB) ℂ) (hρ : Density ρ) (hH : ∀ x, POVM (H x))
    (hK : ∀ y, POVM (K y)) (γ εtol : ℝ) (hγ : 0 < γ ∧ γ < 1) (hε : 0 < εtol ∧ εtol ≤ (1 - γ) / 2)
    (n : ℕ) :
    let δ := deficit G ρ H K
    let ω := quantumValue G
    (γ * δ < εtol →
      ∑ t : Fin n → RoundO X Y A B,
        (if εtol < HybridXorLift.tvDist (freq fun i => recordOf G (t i)) (PC γ ω)
          then ∏ i, honestRecordProb G γ ρ H K (t i) else 0) ≤
        6 * Real.exp (-(8 * (n : ℝ) * (εtol - γ * δ) ^ 2) / 9)) ∧
    ∀ c : Fin n → Option Bool, HybridXorLift.tvDist (freq c) (PC γ ω) ≤ εtol →
      ⌊(1 - γ) * n / 2⌋₊ ≤ (Finset.univ.filter fun i => c i = none).card := by sorry

end FlexRigidity
