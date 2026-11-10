-- Prove2me | Theorems.Thm_BilatMatch_lemma_B_4
-- name    : BilatMatch.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:04.353972+00:00
-- url     : https://prove2.me/theorems/00b6eba5-2fb4-463f-900c-4c15e4a2b5a6
-- title:
--   Lemma B.4 (Report Extension with Normalized Payments) — (i)–(iii), with (20) and (21)
-- statement:
--   Consider finitely many agents with independent priors and downward-closed matching feasibility. In a target market (same graph and family) all types lie in $[L,U]$, and each report domain is a finite ordered grid or the full interval $[L,U]$. Suppose a feasible target mechanism has monotone interim trade probabilities and uses normalized own-report envelope transfers. Then the following extensions to the original market preserve BIC and IIR (on the whole line) and the joint law of payments, weakly increase GFT, and preserve strictly positive-surplus support whenever present:
--
--   1. if the original types lie in $[L,U]$: round finite-domain buyers down and finite-domain sellers up on grids containing $L,U$, full-interval agents unchanged, the rounded marginals being the target priors;
--   2. for original types anywhere: first project to $[L,U]$ and then round as in (i); here the target mechanism trades only on strictly positive-surplus edges;
--   3. if (i) rounds only buyers, on downward grids of mesh at most $\delta$, with seller priors and full report domains unchanged, then
--   $$\mathrm{Rev}_{\mathrm{ext}}=\mathrm{Rev}_{\mathrm{grid}},\qquad 0\le\mathrm{GFT}_{\mathrm{ext}}-\mathrm{GFT}_{\mathrm{grid}}\le R\delta,\tag{20}$$
--   $$\mathrm{FB}(\mathcal I)-R\delta\le\mathrm{FB}(\mathcal I_{\mathrm{grid}})\le\mathrm{FB}(\mathcal I),\tag{21}$$
--   where $R$ is the maximum number of edges in a feasible matching.
--
--   **Formalization Note** The extensions are existential mechanisms on the original market. In (ii) the extension's realized gains may have infinite expectation, so "weakly increase GFT" compares $\mathrm{GFT}_{\mathrm{grid}}$ with the $[0,\infty]$-valued expectation of the extension's (nonnegative) gains. (21) is stated in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: each report domain is a finite ordered support or the full interval [L,U]; grids containing L, U → a finite domain is any finite grid inside [L,U] containing L and U that carries the target prior; reason: the source's finite ordered support containing L and U is such a grid
--   - generalization: the extension preserves BIC, IIR, payment law and GFT → the extension additionally has integrable interim payments, and in (ii) almost surely nonnegative realized gains; reason: extra conclusions; they hold for the paper's extension (own-report payments; traded edges have original surplus at least the positive target surplus)
--   - encoding: weakly increase GFT in (ii) → GFT_grid ≤ the lintegral of the extension's realized gains; reason: in (ii) the extension's gains are nonnegative but need not be integrable
--   - encoding: mesh at most δ → 0 ≤ δ and consecutive grid points of every finite buyer domain differ by at most δ; reason: a mesh bound is nonnegative
--   - encoding: FB(I) − Rδ ≤ FB(I_grid) → FB(I) ≤ FB(I_grid) + Rδ in [0,∞]; reason: same inequality, written without subtraction in [0,∞]
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.4, eqs. (20)–(21), p.33 (pdf p.35)

import Mathlib
import Definitions.Def_BilatMatch_rounding
import Definitions.Def_BilatMatch_FB

open MeasureTheory

namespace BilatMatch

/-- **Lemma B.4 (Report Extension with Normalized Payments).** Liu, Qin, Wang, arXiv:2609.30702
(held version, sha256 ff1490ad…), Lemma B.4, eqs. (20)–(21), p.33 (pdf p.35).

Finitely many agents, independent priors, downward-closed matching feasibility. In a target market
`J` (same graph and family, priors `G`) all types lie in `[L, U]` and each report domain is a finite
ordered grid or the full interval `[L, U]`. Let the target mechanism `A` have monotone interim trade
probabilities and normalized own-report envelope transfers. Then the following extensions to the
original market `I` preserve BIC, IIR (on the whole line) and the joint law of payments, weakly
increase GFT, and preserve strictly positive-surplus support whenever present:
* (i) original types in `[L, U]`; finite-domain buyers rounded down, finite-domain sellers rounded
  up, full-interval agents unchanged; the rounded marginals are the target priors;
* (ii) original types anywhere; project to `[L, U]`, then round as in (i); here `A` trades only on
  strictly positive-surplus edges;
* (iii) in (i), if only buyers are rounded, on grids of mesh at most `δ`, seller priors unchanged,
  then `Rev_ext = Rev_grid`, `0 ≤ GFT_ext − GFT_grid ≤ Rδ` (20) and
  `FB(I) − Rδ ≤ FB(I_grid) ≤ FB(I)` (21).

**Formalization Note**
* A finite domain is any finite grid `D u ⊆ [L, U]` containing `L` and `U`; the target prior is
  carried by `D u`. The extensions are the existential `A'`, with `IsPaymentPreservingExtension`
  collecting BIC, IIR, payment law and positive-surplus preservation.
* In (ii) realized gains of the extension are nonnegative and may have infinite expectation, so
  "weakly increase GFT" compares `GFT_grid` with the `lintegral` of the extension's gains.
* `R` is `maxMatchSize I`; (21) is stated in `ℝ≥0∞`; `0 ≤ δ` is part of "mesh at most `δ`". -/
theorem lemma_B_4 {B S : Type*} [Fintype B] [Fintype S] (I : Market B S) (hI : I.IsValid)
    (L U : ℝ) (hLU : L ≤ U) (G : B ⊕ S → Measure ℝ) (hG : ∀ u, IsProbabilityMeasure (G u))
    (D : B ⊕ S → Set ℝ)
    (hD : ∀ u, ((D u).Finite ∧ L ∈ D u ∧ U ∈ D u ∧ D u ⊆ Set.Icc L U) ∨ D u = Set.Icc L U)
    (hGD : ∀ u, G u (D u)ᶜ = 0) (A : Mechanism (I.withLaws G))
    (hmonoB : ∀ i, MonotoneOn (A.interimXB i) (D (Sum.inl i)))
    (hmonoS : ∀ j, AntitoneOn (A.interimXS j) (D (Sum.inr j)))
    (henv : A.IsNormalizedEnvelope D) :
    ((∀ u, I.law u (Set.Icc L U)ᶜ = 0) → (∀ u, G u = (I.law u).map (roundMap L U D u)) →
      ∃ A' : Mechanism I, IsPaymentPreservingExtension D A A' ∧ A.GFT ≤ A'.GFT) ∧
    ((∀ u, G u = (I.law u).map (roundMap L U D u)) → A.PosSurplusOn (domainProfiles D) →
      ∃ A' : Mechanism I, IsPaymentPreservingExtension D A A' ∧
        (∀ᵐ θ ∂typeMeasure I, 0 ≤ A'.gftIntegrand θ) ∧
        ENNReal.ofReal A.GFT ≤ ∫⁻ θ, ENNReal.ofReal (A'.gftIntegrand θ) ∂typeMeasure I) ∧
    (∀ δ : ℝ, 0 ≤ δ → (∀ u, I.law u (Set.Icc L U)ᶜ = 0) →
      (∀ u, G u = (I.law u).map (roundMap L U D u)) → (∀ j, G (Sum.inr j) = I.sellerLaw j) →
      (∀ i, (D (Sum.inl i)).Finite → ∀ d ∈ D (Sum.inl i), d < U →
        succIn (D (Sum.inl i)) d - d ≤ δ) →
      (∃ A' : Mechanism I, IsPaymentPreservingExtension D A A' ∧ A'.Rev = A.Rev ∧
        0 ≤ A'.GFT - A.GFT ∧ A'.GFT - A.GFT ≤ maxMatchSize I * δ) ∧
      FB I ≤ FB (I.withLaws G) + ENNReal.ofReal (maxMatchSize I * δ) ∧
      FB (I.withLaws G) ≤ FB I) := by sorry

end BilatMatch
