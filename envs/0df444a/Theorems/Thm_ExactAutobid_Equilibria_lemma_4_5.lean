-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_lemma_4_5
-- name    : ExactAutobid.Equilibria.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:57:10.584196+00:00
-- url     : https://prove2.me/theorems/c47e0805-0336-423b-8390-110bd19d7ccd
-- title:
--   Lemma 4.5 — exact realization of the nonlinear second-price ROI gadget
-- statement:
--   Fix a rational cap $A > 1$, $m = A - 1$, $L = 1 + m/4$, and the nonlinear gadget ($k = 1$, $v = L$, $d_1 = 1/16$, $r_1 = A d_1 + m/64$, $t = L - 1$, $x = 5m/64$), with $E_{\mathrm{aux}}(a) = r_1 + x - d_1 a$. There is a function $h$, continuous and strictly decreasing on $[1, A]$, such that for every input $a \in [1,A]$ the value $h(a)$ lies in $(L, A)$ and is the unique solution in $(L, A)$ of
--   $$E_{\mathrm{aux}} = \frac{(\alpha_{\mathrm{out}} - L)^2}{\alpha_{\mathrm{out}} - 1}. \tag{4.2}$$
--   Every equilibrium of every market containing the gadget satisfies (4.2) with $\alpha_{\mathrm{out}} = h(\alpha_{\mathrm{in},1})$, and every input in $[1,A]$ admits a local completion realizing this output and satisfying both core ROI conditions, with the input bidder's upstream ROI condition unchanged.
--
--   This gadget supplies the nonlinear response that Theorem 3.1(i) turns into multiplication.
--
--   Differences from the source:
--   - reading: every equilibrium [of the constructed auction] → every equilibrium of every market containing the gadget pattern IsROIGadget: Table 1's valuations on the gadget goods, A_aux valuing nothing else, and every other good valued by A_out valued more than A times as much by another bidder; reason: in the constructed auction A_out's other goods are downstream input goods with r_i > A d_i; the lemma is stated for every auction with that structure
--   - reading: a local completion satisfying both core ROI conditions; the input bidders' upstream ROI conditions remain unchanged → for every multiplier profile with inputs in [1, A], multipliers for A_out, A_aux and shares on the gadget goods: a valid allocation there, the ROI conditions of A_out and A_aux counted on the gadget goods, and share 0 for every input bidder on every gadget good; reason: explicit form of 'local completion' (Lemma 4.3's proof)
--   - reading: for each input in [1, A], the unique output lies in (L, A) and is continuous and strictly decreasing in the input → ∃ h continuous and strictly decreasing on [1, A] with h(a) ∈ (L, A) the unique solution of (4.2) in (L, A), and α_out = h(α_in,1) in every equilibrium; reason: 'the unique output' is the equilibrium output as a function of the input
--   - encoding: E_aux = r₁ + x − d₁ α_in,1 → A/16 + (A − 1)/64 + 5(A − 1)/64 − α_in,1/16; reason: the constants substituted
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 17 (PDF 19), Lemma 4.5 and (4.2)

import Mathlib
import Definitions.Def_ExactAutobid_Equilibria_ROIPacing

namespace ExactAutobid.Equilibria

/-- **Lemma 4.5 (Exact realization of the nonlinear second-price ROI gadget).** Fix `A > 1`,
`m = A − 1`, `L = 1 + m/4`, and the nonlinear gadget of §4.1.2 (`k = 1`, `v = L`, `d₁ = 1/16`,
`r₁ = A d₁ + m/64`, `t = L − 1`, `x = 5m/64`), with `E_aux(a) = r₁ + x − d₁ a`. There is an
input–output function `h`, continuous and strictly decreasing on `[1, A]`, whose value at each
input is the unique solution in `(L, A)` of (4.2) `E_aux = (α_out − L)²/(α_out − 1)`; every
equilibrium of every market containing the gadget satisfies (4.2) with `α_out = h(α_{in,1})`; and
every input in `[1, A]` admits a local completion realizing this output and satisfying both core ROI
conditions, the input bidder's upstream ROI condition unchanged. -/
theorem lemma_4_5 (A : ℚ) (hA : 1 < A) :
    ∃ h : ℝ → ℝ,
      ContinuousOn h (Set.Icc 1 (A : ℝ)) ∧ StrictAntiOn h (Set.Icc 1 (A : ℝ)) ∧
      (∀ a ∈ Set.Icc 1 (A : ℝ),
        1 + ((A : ℝ) - 1) / 4 < h a ∧ h a < A ∧
        (A : ℝ) / 16 + ((A : ℝ) - 1) / 64 + 5 * ((A : ℝ) - 1) / 64 - a / 16 =
          (h a - (1 + ((A : ℝ) - 1) / 4)) ^ 2 / (h a - 1) ∧
        ∀ u ∈ Set.Ioo (1 + ((A : ℝ) - 1) / 4) (A : ℝ),
          (A : ℝ) / 16 + ((A : ℝ) - 1) / 64 + 5 * ((A : ℝ) - 1) / 64 - a / 16 =
            (u - (1 + ((A : ℝ) - 1) / 4)) ^ 2 / (u - 1) → u = h a) ∧
      ∀ (β γ : Type) [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
        (v : β → γ → ℝ) (inB : Fin 1 → β) (outB auxB : β) (gout gpout gpaux : γ)
        (gin : Fin 1 → γ),
        IsROIGadget (A : ℝ) v 1 (1 + ((A : ℝ) - 1) / 4) (fun _ => 1 / 16)
          (fun _ => (A : ℝ) / 16 + ((A : ℝ) - 1) / 64) (((A : ℝ) - 1) / 4)
          (5 * ((A : ℝ) - 1) / 64) inB outB auxB gout gpout gpaux gin →
        (∀ (α : β → ℝ) (x : β → γ → ℝ), IsROIPacingEq (A : ℝ) v α x →
          (A : ℝ) / 16 + ((A : ℝ) - 1) / 64 + 5 * ((A : ℝ) - 1) / 64 - α (inB 0) / 16 =
            (α outB - (1 + ((A : ℝ) - 1) / 4)) ^ 2 / (α outB - 1) ∧
          α outB = h (α (inB 0))) ∧
        ∀ α : β → ℝ, (1 ≤ α (inB 0) ∧ α (inB 0) ≤ A) →
          ∃ (aOut aAux : ℝ) (y : β → γ → ℝ),
            aOut = h (α (inB 0)) ∧ (1 ≤ aAux ∧ aAux ≤ A) ∧
            IsLocalROICompletion (A : ℝ) v
              (Function.update (Function.update α outB aOut) auxB aAux)
              y inB outB auxB gout gpout gpaux gin := by sorry

end ExactAutobid.Equilibria
