-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_lemma_4_3
-- name    : ExactAutobid.Equilibria.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:56.599122+00:00
-- url     : https://prove2.me/theorems/52120298-cb90-470f-91a3-8adf52b3b0f2
-- title:
--   Lemma 4.3 — exact realization of the affine second-price ROI gadget
-- statement:
--   Fix a rational cap $A > 1$, $m = A - 1$, $L = 1 + m/4$, $k \le 2$ inputs with valuations $d_i > 0$, and a rational $C$ with $C - A\sum_i d_i \ge L$. Consider any second-price ROI pacing market containing the affine gadget of Table 1 with $v = 1$, $r_i = A d_i + m/(16k)$, $t = m/8$, $x = C - 1 - t - \sum_i r_i$. Then every equilibrium satisfies (4.1):
--   $$\alpha_{\mathrm{out}} = \min\Big\{A,\; C - \sum_{i=1}^{k} d_i \alpha_{\mathrm{in},i}\Big\} \in [L, A].$$
--   Conversely, every input assignment in $[1,A]^k$ admits a local completion realizing this output and satisfying both core ROI conditions, and the input bidders receive nothing in the gadget, so their upstream ROI conditions are unchanged.
--
--   This gadget supplies the affine source operations of the ROI pacing reduction (§4.2).
--
--   Differences from the source:
--   - reading: every equilibrium [of the constructed auction] → every equilibrium of every market containing the gadget pattern IsROIGadget: Table 1's valuations on the gadget goods, A_aux valuing nothing else, and every other good valued by A_out valued more than A times as much by another bidder; reason: in the constructed auction A_out's other goods are downstream input goods with r_i > A d_i; the lemma is stated for every auction with that structure
--   - reading: a local completion satisfying both core ROI conditions; the input bidders' upstream ROI conditions remain unchanged → for every multiplier profile with inputs in [1, A], multipliers for A_out, A_aux and shares on the gadget goods: a valid allocation there, the ROI conditions of A_out and A_aux counted on the gadget goods, and share 0 for every input bidder on every gadget good; reason: explicit form of 'local completion' (Lemma 4.3's proof)
--   - encoding: k ∈ {0, 1, 2} inputs A_in,1, A_in,2 → k ≤ 2 and injective role maps Fin k → bidders, Fin k → goods; empty sums are zero; reason: Lean convention
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 15 (PDF 17), Lemma 4.3 and (4.1)

import Mathlib
import Definitions.Def_ExactAutobid_Equilibria_ROIPacing

namespace ExactAutobid.Equilibria

/-- **Lemma 4.3 (Exact realization of the affine second-price ROI gadget).** In every market
containing the affine gadget of Table 1 (`v = 1`; `m = A − 1`, `L = 1 + m/4`, input valuations
`d_i > 0`, `C − A Σ d_i ≥ L`, `r_i = A d_i + m/(16k)`, `t = m/8`, `x = C − 1 − t − Σ r_i`), every
equilibrium satisfies (4.1): `α_out = min{A, C − Σ d_i α_{in,i}} ∈ [L, A]`. Conversely, every input
assignment in `[1, A]^k` admits a local completion realizing this output and satisfying both core
ROI conditions, with the input bidders' upstream ROI conditions unchanged. -/
theorem lemma_4_3 {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (A : ℚ) (hA : 1 < A) (k : ℕ) (hk : k ≤ 2) (d : Fin k → ℚ) (hd : ∀ i, 0 < d i) (C : ℚ)
    (hC : 1 + ((A : ℝ) - 1) / 4 ≤ (C : ℝ) - (A : ℝ) * ∑ i, (d i : ℝ))
    (v : β → γ → ℝ) (inB : Fin k → β) (outB auxB : β) (gout gpout gpaux : γ) (gin : Fin k → γ)
    (hG : IsROIGadget (A : ℝ) v k 1 (fun i => (d i : ℝ))
      (fun i => (A : ℝ) * d i + ((A : ℝ) - 1) / (16 * k))
      (((A : ℝ) - 1) / 8)
      ((C : ℝ) - 1 - ((A : ℝ) - 1) / 8 - ∑ i, ((A : ℝ) * d i + ((A : ℝ) - 1) / (16 * k)))
      inB outB auxB gout gpout gpaux gin) :
    (∀ (α : β → ℝ) (x : β → γ → ℝ), IsROIPacingEq (A : ℝ) v α x →
      α outB = min (A : ℝ) ((C : ℝ) - ∑ i, (d i : ℝ) * α (inB i)) ∧
        1 + ((A : ℝ) - 1) / 4 ≤ α outB ∧ α outB ≤ A) ∧
    ∀ α : β → ℝ, (∀ i, 1 ≤ α (inB i) ∧ α (inB i) ≤ A) →
      ∃ (aOut aAux : ℝ) (y : β → γ → ℝ),
        aOut = min (A : ℝ) ((C : ℝ) - ∑ i, (d i : ℝ) * α (inB i)) ∧
        (1 ≤ aOut ∧ aOut ≤ A) ∧ (1 ≤ aAux ∧ aAux ≤ A) ∧
        IsLocalROICompletion (A : ℝ) v (Function.update (Function.update α outB aOut) auxB aAux)
          y inB outB auxB gout gpout gpaux gin := by sorry

end ExactAutobid.Equilibria
