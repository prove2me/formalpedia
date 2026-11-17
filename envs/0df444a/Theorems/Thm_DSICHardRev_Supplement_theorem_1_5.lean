-- Prove2me | Theorems.Thm_DSICHardRev_Supplement_theorem_1_5
-- name    : DSICHardRev.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:12:15.436203+00:00
-- url     : https://prove2.me/theorems/8db860b9-a612-46e9-bf8b-2e64c9037dc1
-- title:
--   Theorem 1.5 — IR, NNT, universally DSIC $0.9999$-approximation for two weighted matroid rank valuations needs $2^{\Omega(m)}$ communication
-- statement:
--   Consider two bidders with weighted matroid rank valuations on $m$ items with values in the range $R$ of p.8, and randomized mechanisms given as probability distributions $\mu$ over deterministic mechanisms.
--
--   **Theorem.** There are $c>0$ and $m_0$ such that for every $m\ge m_0$ and every distribution $\mu$ over deterministic mechanisms for two bidders on $m$ items such that
--   1. every mechanism in the support of $\mu$ is individually rational, has no negative transfers and is dominant-strategy incentive compatible on $\mathcal D_{\mathrm{WMR}}(m)$, and
--   2. on every profile from $\mathcal D_{\mathrm{WMR}}(m)$, $\ \mathbb E_\mu[\text{welfare}]\ge 0.9999\cdot\mathrm{OPT}$,
--
--   some mechanism in the support of $\mu$ uses at least $2^{cm}$ bits of communication.
--
--   Weighted matroid rank valuations are gross substitutes and hence admit deterministic welfare-maximizing truthful mechanisms (p.3); the theorem shows that dominant-strategy incentive compatibility, even randomized, costs exponential communication already for two bidders.
--
--   **Formalization Note** "Exponential communication" is read as $2^{\Omega(m)}$. The communication of a universally DSIC mechanism is its worst case over the support, so the conclusion asserts one support element with at least $2^{cm}$ bits, not all of them. `Fin m` counts all items, including the two special items of the construction in Appendix B.
--
--   Differences from the source:
--
--   - reading: uses exponential communication → ∃ c > 0, ∃ m₀, ∀ m ≥ m₀: some mechanism in the support of μ has 2^{c·m} ≤ comm; reason: standard reading of 'exponential' as 2^{Ω(m)}; the communication of a randomized mechanism is the worst case over its randomness (Definition 2.7)
--   - encoding: universally DSIC mechanism (Definition 2.12): can be written as a distribution over deterministic DSIC mechanisms → a PMF μ over deterministic Mechanism (Fin 2) (Fin m) whose every support element is IR, NNT and DSIC on DWMR m; reason: μ is the witnessing distribution; IR and NNT guarantee their property on every outcome (Definitions 2.8, 2.9, p.9), hence on every support element
--   - encoding: weighted matroid rank valuations 2^M → ℝ+ → weighted matroid rank valuations on Fin m with every value in Rset m; reason: the paper's global range assumption (p.8)
--   - encoding: E[welfare] ≥ 0.9999 · max_T welfare → (9999/10000) · welfare v T ≤ expWelfare μ v for every disjoint T; reason: no maximum or division; same instances
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), Theorem 1.5, p.3 (proof App. B, pp.31–36)

import Mathlib
import Definitions.Def_DSICHardRev_Protocol
import Definitions.Def_DSICHardRev_Supplement_Domains
import Definitions.Def_DSICHardRev_Supplement_RandMechanism

namespace DSICHardRev

namespace Supplement

/-- **Theorem 1.5** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §1.2, p.3; proof App. B, pp.31–36):
any IR, NNT, universally DSIC mechanism attaining a `0.9999`-approximation for two weighted matroid
rank valuations uses exponential communication.

**Formalization Note.** "Exponential communication" is read as `2^{Ω(m)}`: there are `c > 0` and
`m₀` such that for every `m ≥ m₀` and every distribution `μ` over deterministic mechanisms for two
bidders on the items `Fin m` whose every support mechanism is IR, NNT and DSIC (against all
strategy profiles) on `DWMR m` (weighted matroid rank valuations with values in the range `R` of
p.8), and with `0.9999 · OPT ≤ E[welfare]` on every profile from `DWMR m`, the worst-case
communication is at least `2^{c m}`: some mechanism in the support of `μ` uses at least `2^{c m}`
bits. `Fin m` counts all items (App. B's two special items included). -/
theorem theorem_1_5 :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ μ : RandMechanism (Fin 2) (Fin m),
        RandMechanism.IsIRNNTUnivDSIC μ (DWMR m) →
        RandMechanism.IsApproxRatio μ (DWMR m) (9999 / 10000) →
        ∃ M ∈ PMF.support μ, (2 : ℝ) ^ (c * (m : ℝ)) ≤ (M.comm : ℝ) := by sorry

end Supplement

end DSICHardRev
