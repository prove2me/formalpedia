-- Prove2me | Theorems.Thm_BlindNRMLS_dlp_upper_bound
-- name    : BlindNRMLS.dlp_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:12.762877+00:00
-- url     : https://prove2.me/theorems/2aae1342-b4db-4e75-9df4-64fc738a3fa9
-- title:
--   §3.1, p.10 (corrected: factor $1+\max_i\sum_ja_{ij}/B_i$, since the DLP alone fails under the stopping rule) — DLP bound for any policy
-- statement:
--   Let all inventories be positive. For every demand distribution $Q$ and every policy $\pi$,
--   $$
--   \mathrm{Rev}_Q(\pi)\le\Big(1+\max_i\frac{\sum_j a_{ij}}{B_i}\Big)J^{\mathrm{DLP}} .
--   $$
--   The factor is $1$ when $d=0$. This is the benchmark inequality that comparisons to the LP rest on.
--
--   Differences from the source:
--   - correction: the DLP is an upper bound on the expected revenue of any policy → Rev ≤ (1 + max_i Σ_j a_ij/B_i) J^DLP, for B_i > 0; reason: a period is lost only once demand exceeds B: one arm, p=(1,0,0), a=(0,1,0), B=1, T=3, Q₁≡1, Q₂~Ber(½) has J=2 and expected revenue 2.25
--   - reading: the model does not say whether the demands of different products in one period are independent → the joint law under arm k is the product of the marginal laws on [0,1]; reason: p.2 says demand is independent, p.20 has q determine a Bernoulli instance, and the clean event and Lemma EC.6 need it
--   - reading: selling stops when the cumulative demand of a resource exceeds its inventory → a period earns revenue iff consumption through it is within B; reason: the display of the effective horizon on p.ec22 fixes this; the violating period earns nothing
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, §3.1, p.10

import Mathlib
import Definitions.Def_BlindNRMLS_switchRegret

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- The DLP bound (corrected): for positive inventories, every policy under every `Q` has
`Rev_Q(π) ≤ (1 + max_i (∑_j a_{ij})/B_i) J^DLP`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, §3.1, p.10.

**Formalization Note.** The page asserts `Rev_Q(π) ≤ J^DLP`, which fails under its stopping rule,
because a period is lost only once cumulative demand exceeds `B`. The factor is what stopping one
period later costs. For `d = 0` the supremum over the empty index is `0`, and the factor is `1`. -/
theorem dlp_upper_bound {d n K : ℕ} (P : Problem d n K) (Q : DemandLaw n K) (π : Policy n K)
    (hB : ∀ i, 0 < P.B i) :
    Rev P Q π ≤ (1 + ⨆ i, (∑ j, P.A i j) / P.B i) * J P Q := by sorry

end BlindNRMLS
