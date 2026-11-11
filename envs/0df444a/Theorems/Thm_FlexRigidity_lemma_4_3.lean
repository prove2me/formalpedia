-- Prove2me | Theorems.Thm_FlexRigidity_lemma_4_3
-- name    : FlexRigidity.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:21:32.388913+00:00
-- url     : https://prove2.me/theorems/a90e4146-d601-4c8f-8841-88626555ead9
-- title:
--   Lemma 4.3 — the block function $h_{i,c}$
-- statement:
--   Under Postulate Set 4.1, for $\alpha>1$ and a normalized pure input $|\sigma^i\rangle_{M_iR_i}$, let
--   $$h_{i,c}(|\sigma^i\rangle)=Q_\alpha\big(\sigma^{i,\mathcal G_i}_{\wedge(C_i=c)}\big\|\sigma^{i,\mathcal P_i\circ\mathcal G_i}_{\wedge(C_i=c)}\big).$$
--   When $P_{C_i}(c)>0$ this equals $P_{C_i}(c)\,2^{(\alpha-1)D_\alpha(\sigma^{i,\mathcal G_i}_{|c}\|\sigma^{i,\mathcal P_i\circ\mathcal G_i}_{|c})}$. Moreover:
--
--   1. $h_{i,c}$ depends only on the marginal $\sigma^i_{M_i}$, so it may be written $h_{i,c}(\sigma^i_{M_i})$;
--   2. $h_{i,c}$ is concave in $\sigma^i_{M_i}$;
--   3. $h_{i,c}$ is continuous at every positive definite $\sigma^i_{M_i}$.
--
--   These are the properties used in the minimax argument of Lemma 4.2.
--
--   **Formalization Note** Item 1 is stated as: for a pure input on any finite reference, $h_{i,c}$ equals its value on the canonical purification of the marginal (`hMarg`). Items 2 and 3 are stated for `hMarg`: concavity over finite mixtures of states, and continuity within the state space $S_=(M_i)$. Values in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: Lemma 4.3 states no range of α → α > 1; reason: the order of §4.1 (Lemma 4.2, Fact 2.7's default), the only order at which h_{i,c} is used
--   - encoding: h_{i,c} as a function of σ^i_{M_i} → hMarg, h_{i,c} on the canonical purification with R ≅ M_i; concavity and continuity are stated for it; reason: by item (i) the choice of purification does not matter
--   - encoding: continuity at positive definite σ^i_{M_i} of a function on S_=(M_i) → ContinuousWithinAt on the set of density matrices, values in [0, ∞]; reason: h_{i,c} is defined on states; for finite values continuity in [0, ∞] is continuity in ℝ
--   - reading: T_i "only uses C_i as a control register" (Postulate 4.1(i)) → T_i maps every operator supported on the block C_i = c to an operator supported on the output block C_i = c; reason: the property the proof uses (p. 29, "Since T_i preserves C_i"); every T_i that uses C_i as a control register has it
--   - encoding: P_i of the form (16), specified on Z_i-classical inputs → ctrlReplacer, which pinches Z_i first and then acts as (16); reason: G_i has classical output Z_i, so P_i ∘ G_i and F_i are unchanged
--   - encoding: rounds i = 1, …, n with registers of varying dimension → families indexed by all i ∈ ℕ (Lean rounds 0, …, n−1), of which the statement uses the first n; registers are finite types; reason: Lean convention; data for later rounds are never used, and every finite family extends
--   - encoding: divergences and channel divergences with values in [0, +∞] → values in EReal (extended reals); reason: Lean convention; the +∞ conventions of Definition 2.7 are kept, no instance changes
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 4.3, eq. (21), p. 30

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_hBlock
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_FlexRigidity_exp2E
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 4.3** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256
8c67699d…, p. 30). Under Postulate Set 4.1 and `α > 1`, for a normalized pure input `|σ^i⟩_{M_iR_i}`
let `h_{i,c}(|σ^i⟩) = Q_α(σ^{i,G_i}_{∧(C_i=c)} ‖ σ^{i,P_i∘G_i}_{∧(C_i=c)})` (21). When
`P_{C_i}(c) > 0` this is `P_{C_i}(c) 2^{(α−1) D_α(σ^{i,G_i}_{|c} ‖ σ^{i,P_i∘G_i}_{|c})}`, and
(i) `h_{i,c}` depends only on the marginal `σ^i_{M_i}`; (ii) it is concave in `σ^i_{M_i}`;
(iii) it is continuous at every positive definite `σ^i_{M_i}`.

**Formalization Note** (i) is stated as: for a pure input on any finite reference `R_f`, `h_{i,c}`
equals `hMarg` of its marginal, where `hMarg` evaluates `h_{i,c}` on the canonical purification.
(ii) is concavity over finite mixtures of states and (iii) continuity within the state space,
both for `hMarg` (values in `ℝ≥0∞`; the extended `2^{(α−1)D}` is `exp2E`). -/
theorem lemma_4_3 {C : Type} {O M Z S J : ℕ → Type} [Fintype C] [DecidableEq C]
    [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
    [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)] [∀ k, Fintype (Z k)] [∀ k, DecidableEq (Z k)]
    [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)] [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (D : SeqData C O M Z S J) (n : ℕ) (hD : D.IsPostulate41 n) (i : ℕ) (hi : i < n) (c : C)
    (α : ℝ) (hα : 1 < α) :
    (∀ (Rf : Type) [Fintype Rf] [DecidableEq Rf] (σ : Rf × M i → ℂ), DHRUniq.IsUnitVec σ →
      let σG := idTensorSuperop (R := Rf) (D.G i) (ObliviousRSP.pureState σ)
      let σPG := idTensorSuperop (R := Rf) (fun X => D.P i (D.G i X)) (ObliviousRSP.pureState σ)
      let p := tr (blockC (D.cOf i) c σG)
      0 < p → hBlock D i c α σ = ENNReal.ofReal p *
        exp2E (((α - 1 : ℝ) : EReal) * divergence α (((p⁻¹ : ℝ) : ℂ) • blockC (D.cOf i) c σG)
          (((p⁻¹ : ℝ) : ℂ) • blockC (D.cOf i) c σPG))) ∧
    (∀ (Rf : Type) [Fintype Rf] [DecidableEq Rf] (σ : Rf × M i → ℂ), DHRUniq.IsUnitVec σ →
      hBlock D i c α σ = hMarg D i c α (rightMarginal (ObliviousRSP.pureState σ))) ∧
    (∀ (k : ℕ) (t : Fin k → ℝ) (ρs : Fin k → Matrix (M i) (M i) ℂ),
      (∀ j, 0 ≤ t j) → ∑ j, t j = 1 → (∀ j, Density (ρs j)) →
      ∑ j, ENNReal.ofReal (t j) * hMarg D i c α (ρs j) ≤
        hMarg D i c α (∑ j, ((t j : ℝ) : ℂ) • ρs j)) ∧
    (∀ ρ : Matrix (M i) (M i) ℂ, Density ρ → ρ.PosDef →
      ContinuousWithinAt (hMarg D i c α) {ρ' | Density ρ'} ρ) := by sorry

end FlexRigidity
