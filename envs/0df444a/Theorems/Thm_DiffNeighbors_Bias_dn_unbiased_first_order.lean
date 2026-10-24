-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_dn_unbiased_first_order
-- name    : DiffNeighbors.Bias.dn_unbiased_first_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:41:25.531267+00:00
-- url     : https://prove2.me/theorems/2c977e2d-0ab0-45a1-bd8d-0e804d23c3f6
-- title:
--   §3.3, p. 11 — E[ATE_DN] equals the average over nodes of the first-order Taylor approximation of F¹_i(1) − F⁰_i(0)
-- statement:
--   Under the Bernoulli design ($Z_l$ i.i.d. Bernoulli$(p)$, $0 < p < 1$), let $F^a_i(p) = \mathbb E[f^a_i(Z)]$ for unit $i$'s conditional outcome function $f^a_i$. The first-order approximation of node $i$'s contribution $F^1_i(1) - F^0_i(0)$ to the ATE (p. 10) is
--   $$A_i = F^1_i(p) + \sum_{j \in \mathcal N_i} (1 - p)\bigl(\mathbb E[f^1_i(Z) \mid Z_j = 1] - \mathbb E[f^1_i(Z) \mid Z_j = 0]\bigr) - F^0_i(p) - \sum_{j \in \mathcal N_i} (0 - p)\bigl(\mathbb E[f^0_i(Z) \mid Z_j = 1] - \mathbb E[f^0_i(Z) \mid Z_j = 0]\bigr).$$
--   The DN estimator (3) is an unbiased estimate of the average of these approximations:
--   $$\mathbb E[\mathrm{ATE}_{\mathrm{DN}}] = \frac1N \sum_{i=1}^N A_i.$$
--
--   This is the first half of the proof of Theorem 1: the bias of DN is the error of a first-order Taylor approximation, which the second half bounds through second-order differences.
--
--   Differences from the source:
--   - encoding: "the DN estimator is a unbiased estimate of a first order approximation to the ATE" → E[ATE_DN] = (1/N) Σ_i A_i with A_i the p. 10 display "Taken together, …" written out term by term; reason: the sentence's content with the approximation the proof defines on p. 10; the factor (0 − p) is copied as printed
--   - generalization: outcomes under Assumption 1 (standing) → any outcome functions, with no Assumption 1; reason: the identity holds for arbitrary outcome functions (it uses only the design and the symmetry of G); it specializes to the paper's setting
--   - encoding: a Bernoulli(p) design whose weights divide by p and 1 − p → hypotheses 0 < p and p < 1; reason: the weights 1/p and 1/(1 − p) and the design presuppose p ∈ (0,1); this only excludes undefined cases
--   - encoding: E[·] over z_i i.i.d. Bernoulli(p) → bernExp p h = Σ_z (Π_j (p if z_j = 1 else 1 − p)) h(z), a finite sum; reason: the law of the design on the finite set {0,1}^N; same values
--   - encoding: f^a_i as a function of z_{N_i}; E[f^a(Z) | Z_j = b] and E[f^a(Z) | Z_j = b, Z_k = c] → condOutcome f i a z = f_i(z with z_i := a), a function on all of {0,1}^N; conditional expectations are bernExp of the function with the conditioned coordinates overwritten by Function.update; reason: under Assumption 1 condOutcome f i a depends only on z_{N_i}; by independence of the coordinates, conditioning on Z_j = b is the same as setting z_j := b
--   - encoding: units [N] = {1,…,N}, treatment vectors z ∈ {0,1}^N, an undirected graph without self-loops, d = max_i |N_i| → a finite type ι with N = card ι, z : ι → Bool with 1/0 read through ind, G : SimpleGraph ι, N_i = G.neighborFinset i, d = G.maxDegree; reason: a simple graph is exactly an undirected graph without self-loops; same instances
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 11, §3.3 (proof of Theorem 1), 'In summary: the DN estimator is a unbiased estimate of a first order approximation to the ATE', with the approximation of p. 10 ('Taken together, we have a first-order approximation of node i's contribution to the ATE')

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

namespace DiffNeighbors.Bias

open Finset

/-- **The DN estimator is an unbiased estimate of a first-order approximation to the ATE**,
§3.3, pp. 10–11. Node `i`'s first-order approximation (p. 10) is
`F¹(p) + ∑_{j∈N_i} (1 − p)(E[f¹(Z)|Z_j = 1] − E[f¹(Z)|Z_j = 0])
  − F⁰(p) − ∑_{j∈N_i} (0 − p)(E[f⁰(Z)|Z_j = 1] − E[f⁰(Z)|Z_j = 0])`,
and `E[ATE_DN]` is its average over the nodes. -/
theorem dn_unbiased_first_order {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (f : ι → (ι → Bool) → ℝ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    bernExp p (dnEstimator G p f) = (Fintype.card ι : ℝ)⁻¹ * ∑ i,
      (bernExp p (condOutcome f i true)
        + ∑ j ∈ G.neighborFinset i, (1 - p) *
            (bernExp p (fun z => condOutcome f i true (Function.update z j true))
              - bernExp p (fun z => condOutcome f i true (Function.update z j false)))
        - bernExp p (condOutcome f i false)
        - ∑ j ∈ G.neighborFinset i, (0 - p) *
            (bernExp p (fun z => condOutcome f i false (Function.update z j true))
              - bernExp p (fun z => condOutcome f i false (Function.update z j false)))) := by sorry

end DiffNeighbors.Bias
