-- Prove2me | Theorems.Thm_BilatMatch_Supplement_theorem_3_9
-- name    : BilatMatch.Supplement.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:29:18.59079+00:00
-- url     : https://prove2.me/theorems/578790ca-f892-4b0b-bfb4-9cefabb041f4
-- title:
--   Theorem 3.9 (Restricted Bilateral-to-Matching Reduction) — bilateral bounds on $\mathfrak B\times\mathfrak S_\alpha$ transfer to markets with grid-approximable buyers
-- statement:
--   Fix $\alpha,\beta\ge0$, a seller class $\mathfrak S_\alpha$ (bounded seller priors with finite support or regular with interval support, preserved by full-prior regularization followed by conditioning on any positive-mass initial cap) and a buyer class $\mathfrak B$ (finite buyer priors, closed under strictly positive reweighting on each fixed support). Suppose
--   $$V_\alpha(F_B,F_S)\ \ge\ \beta\,\mathrm{FB}(F_B,F_S)\qquad\text{for all }F_B\in\mathfrak B,\ F_S\in\mathfrak S_\alpha .$$
--   Then every matching market $\mathcal I$ with countably many buyers and sellers, a nonempty downward-closed family of feasible matchings, independent priors and $\mathrm{FB}(\mathcal I)<\infty$, whose seller priors lie in $\mathfrak S_\alpha$ and whose buyer priors are bounded and admit downward finite-grid approximations of vanishing mesh with induced priors in $\mathfrak B$, satisfies
--   $$V_\alpha(\mathcal I)\ \ge\ \beta\,\mathrm{FB}(\mathcal I).$$
--
--   This is the version of the bilateral-to-matching reduction for restricted prior classes; the MHR bounds of Theorem 4.1 are transferred to matching markets through it.
--
--   **Formalization Note** $V_\alpha$ is the whole-line supremum of $\mathrm{GFT}+\alpha\,\mathrm{Rev}$ over admissible BIC/IIR mechanisms (no budget constraint); $\beta\,\mathrm{FB}$ is $\beta$ times the real value of the finite first best.
--
--   Differences from the source:
--   - generalization: bounded buyer priors admitting downward finite-grid approximations of vanishing mesh whose induced priors belong to 𝔅 → IsGridApprox 𝔅: bounded, and for every δ > 0 a finite grid with a grid point below and rounding loss t − floorTo G t ≤ δ for almost every type, with induced prior μ.map (floorTo G) ∈ 𝔅; reason: more general than the page; a downward grid of mesh at most δ that reaches below the support has rounding loss at most δ, so every prior the page admits satisfies IsGridApprox, and the theorem specializes to the claim on the page; the proof (eq. (20)–(21) of Lemma B.4(iii), loss at most Rδ) uses only this per-type rounding loss, so the larger class is still covered
--   - encoding: matching markets (§2) → countable B, S, a valid Market (nonempty downward-closed family of matchings, Borel probability priors); reason: the §2 model; independence is the product prior
--   - encoding: V_α and FB of a market with general priors → whole-line Valpha (EReal supremum over admissible BIC/IIR mechanisms) and FB as a lintegral, with FB < ∞ as a hypothesis; reason: the published base conventions; p.7 defines V_α for general priors as this supremum and p.6 assumes FB < ∞
--   - encoding: 𝔖_α, 𝔅 as above (p.14) → the published IsSellerClass α, IsBuyerClass; reason: the base chunk's definitions of these classes
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), Theorem 3.9, p.16 (pdf p.18); classes 𝔖_α, 𝔅 p.14 (pdf p.16)

import Mathlib
import Definitions.Def_BilatMatch_priorClasses
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_FB
import Definitions.Def_BilatMatch_bilateral
import Definitions.Def_BilatMatch_Supplement_IsGridApprox

open MeasureTheory

namespace BilatMatch.Supplement

open BilatMatch

/-- **Theorem 3.9 (Restricted Bilateral-to-Matching Reduction).** Liu, Qin, Wang, *From Bilateral
Trade to Matching Markets: Sharp Gains from Trade*, arXiv:2609.30702 (held version, sha256
ff1490ad…), Theorem 3.9, p.16 (pdf p.18); the classes `𝔖_α`, `𝔅` of p.14 (pdf p.16).

Fix `α, β ≥ 0`, a seller class `𝔖_α` and a buyer class `𝔅`. If `V_α(F_B, F_S) ≥ β FB(F_B, F_S)` for
every bilateral trade with `F_B ∈ 𝔅` and `F_S ∈ 𝔖_α`, then `V_α(I) ≥ β FB(I)` for every matching
market `I` with countably many buyers and sellers, a nonempty downward-closed feasible family,
independent priors, `FB(I) < ∞`, seller priors in `𝔖_α`, and bounded buyer priors admitting downward
finite-grid approximations of vanishing mesh whose induced priors belong to `𝔅`.

**Formalization Note**
* `𝔖_α`, `𝔅` are the published `IsSellerClass α`, `IsBuyerClass` (p.14). `V_α` is the whole-line
  `Valpha` (as in Theorem 1.1); `FB` is a `lintegral`, and `FB(I) < ∞` is the paper's standing
  assumption (p.6).
* The grid condition is `IsGridApprox 𝔅` (boundedness included): for every `δ > 0` a finite grid with
  rounding loss at most `δ` on almost every type and induced prior in `𝔅`. -/
theorem theorem_3_9 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (𝔖 𝔅 : Set (Measure ℝ))
    (h𝔖 : IsSellerClass α 𝔖) (h𝔅 : IsBuyerClass 𝔅)
    (hbil : ∀ GB ∈ 𝔅, ∀ GS ∈ 𝔖,
      ((β * (FB (bilateral GB GS)).toReal : ℝ) : EReal) ≤ Valpha (bilateral GB GS) α)
    {B S : Type*} [Countable B] [Countable S] (I : Market B S) (hI : I.IsValid)
    (hfin : FB I < ⊤) (hS : ∀ j, I.sellerLaw j ∈ 𝔖) (hB : ∀ i, IsGridApprox 𝔅 (I.buyerLaw i)) :
    ((β * (FB I).toReal : ℝ) : EReal) ≤ Valpha I α := by sorry

end BilatMatch.Supplement
