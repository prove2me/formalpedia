-- Prove2me | Theorems.Thm_BilatMatch_proposition_3_7
-- name    : BilatMatch.proposition_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:13:24.744994+00:00
-- url     : https://prove2.me/theorems/18d61a33-82fc-49c0-b7ff-2e9e1960187d
-- title:
--   Proposition 3.7 (Seller Regularization) — $V_\alpha(\mathcal I)=V_\alpha(\hat{\mathcal I}^\alpha)$ and $\mathrm{FB}(\mathcal I)\le\mathrm{FB}(\hat{\mathcal I}^\alpha)$
-- statement:
--   Fix $\alpha\ge0$ and a market $\mathcal I$ with finitely many agents, a nonempty downward-closed family of matchings, finitely supported buyer priors, and seller priors that either have finite support or are regular with interval support (§3.2). Replacing each finite seller prior by its reconstruction, an $\alpha$-weakly regular prior with the same atom probabilities, yields a market $\hat{\mathcal I}^\alpha$ such that
--   $$V_\alpha(\mathcal I)=V_\alpha(\hat{\mathcal I}^\alpha),\qquad \mathrm{FB}(\mathcal I)\le\mathrm{FB}(\hat{\mathcal I}^\alpha).$$
--
--   **Formalization Note** $\hat{\mathcal I}^\alpha$ is the specific reconstruction of p.31; sellers with interval support are unchanged. $V_\alpha$ uses whole-line reports.
--
--   Differences from the source:
--   - reading: replacing the finite seller priors by α-weakly regular priors with the same atom probabilities → replacing each finite seller prior by the reconstruction of p.31, and asserting that it is α-weakly regular with the same atom probabilities; reason: the text after the proposition and its proof identify the replacement as this reconstruction; an existential replacement would be weaker
--   - reading: V_α of a finite-agent market (general definition, p.7) → V_α with BIC/IIR at every real type and report; reason: the paper's mechanisms are built with whole-line BIC/IIR (eq. (1), Lemma B.4); for finite priors the support-restricted and whole-line values coincide (Lemma B.4(i)), so the hypothesis is unchanged and the conclusion takes the stronger reading
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Proposition 3.7, eq. (9), p.14 (pdf p.16)

import Mathlib
import Definitions.Def_BilatMatch_reconLaw
import Definitions.Def_BilatMatch_sellerCost
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_FB

open MeasureTheory

namespace BilatMatch

/-- **Proposition 3.7 (Seller Regularization).** Liu, Qin, Wang, arXiv:2609.30702 (held version,
sha256 ff1490ad…), Proposition 3.7, eq. (9), p.14 (pdf p.16).

For `α ≥ 0` and a market `I` with finitely many agents, finitely supported buyer priors, and seller
priors that have finite support or are regular with interval support (§3.2), replacing each finite
seller prior by its reconstruction (an `α`-weakly regular prior with the same atom probabilities)
yields a market `Î^α` with `V_α(I) = V_α(Î^α)` and `FB(I) ≤ FB(Î^α)`.

**Formalization Note** `Î^α` is `regularizedMarket α I`: the specific reconstruction of p.31 (Lemma
B.2) for finite sellers, sellers with interval support unchanged. `V_α` has whole-line reports (the
general definition, p.7). -/
theorem proposition_3_7 (α : ℝ) (hα : 0 ≤ α) {B S : Type*} [Fintype B] [Fintype S]
    (I : Market B S) (hI : I.IsValid) (hB : ∀ i, IsFiniteSupport (I.buyerLaw i))
    (hS : ∀ j, IsFiniteSupport (I.sellerLaw j) ∨ IsRegularIntervalSeller α (I.sellerLaw j)) :
    (∀ j, IsFiniteSupport (I.sellerLaw j) →
      IsAlphaWeaklyRegular α (reconLaw α (I.sellerLaw j)) (atoms (reconLaw α (I.sellerLaw j)))
        (alphaVirtualCost α (reconLaw α (I.sellerLaw j))) ∧
      ∀ k < nAtoms (I.sellerLaw j), reconLaw α (I.sellerLaw j) {reconCost α (I.sellerLaw j) k} =
        I.sellerLaw j {sortedAtom (I.sellerLaw j) k}) ∧
    Valpha I α = Valpha (regularizedMarket α I) α ∧
    FB I ≤ FB (regularizedMarket α I) := by sorry

end BilatMatch
