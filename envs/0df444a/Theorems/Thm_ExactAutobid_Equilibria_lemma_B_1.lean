-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_lemma_B_1
-- name    : ExactAutobid.Equilibria.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:55:54.207194+00:00
-- url     : https://prove2.me/theorems/e69cf4ee-5838-4c6c-97fa-346b76534a16
-- title:
--   Lemma B.1 — coupling local choices into at most 1 + Σ(k_j − 1) global orders with the same expected payments
-- statement:
--   Consider $m$ local choice locations with $k_j \ge 1$ choices at location $j$, a map combining every tuple $c = (c_1,\dots,c_m)$ of local choices into a valid global order $\mathrm{comb}(c)$, and bidder payments additive over the local choices, $\mathrm{pay}_i(\mathrm{comb}(c)) = \sum_j f_{ij}(c_j)$. Then for any prescribed local marginal distributions $\mu_1, \dots, \mu_m$ there are $s \le 1 + \sum_{j=1}^m (k_j - 1)$ tuples $t_1, \dots, t_s$ and weights $w_\ell \ge 0$ summing to one with marginals $\mu_j$ at every location, whose global orders $\mathrm{comb}(t_\ell)$ are valid and give the same expected payments:
--   $$\sum_{\ell=1}^{s} w_\ell\, \mathrm{pay}_i(\mathrm{comb}(t_\ell)) = \sum_{j=1}^m \sum_{c} \mu_j(c)\, f_{ij}(c).$$
--
--   This is the coupling that turns the local tie choices of the GSP gadgets into a single distribution over legal global orders with polynomial support.
--
--   Differences from the source:
--   - encoding: realized by at most 1 + Σ(k_j − 1) global orders → a weighted list of s ≤ 1 + Σ_j (k_j − 1) local-choice tuples t_ℓ, whose combined orders comb(t_ℓ) form the support, with the prescribed marginals; reason: the orders realized are the images of the listed tuples
--   - encoding: with the same expected payments → Σ_ℓ w_ℓ pay_i(comb(t_ℓ)) = Σ_j Σ_c μ_j(c) f_ij(c) for every bidder i; reason: the expected payment under any coupling of the marginals
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 58 (PDF 60), Lemma B.1

import Mathlib

namespace ExactAutobid.Equilibria

/-- **Lemma B.1 (Coupling Local Choices, [HLN26]).** Let there be `m` local choice locations with
`k_j ≥ 1` choices at location `j`, such that every tuple of local choices combines into a valid
global order, and every bidder's payment is a sum of functions of the individual local choices.
Then any prescribed local marginal distributions are realized by at most `1 + Σ_j (k_j − 1)`
global orders, with the same expected payments. -/
theorem lemma_B_1 {O ι : Type} (valid : O → Prop) (pay : ι → O → ℝ) (m : ℕ) (k : Fin m → ℕ)
    (hk : ∀ j, 1 ≤ k j) (comb : ((j : Fin m) → Fin (k j)) → O) (hcomb : ∀ c, valid (comb c))
    (f : ι → (j : Fin m) → Fin (k j) → ℝ) (hpay : ∀ i c, pay i (comb c) = ∑ j, f i j (c j))
    (μ : (j : Fin m) → Fin (k j) → ℝ) (hμ0 : ∀ j c, 0 ≤ μ j c) (hμ1 : ∀ j, ∑ c, μ j c = 1) :
    ∃ (s : ℕ) (t : Fin s → (j : Fin m) → Fin (k j)) (w : Fin s → ℝ),
      s ≤ 1 + ∑ j, (k j - 1) ∧ (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
      (∀ j c, ∑ l ∈ Finset.univ.filter (fun l => t l j = c), w l = μ j c) ∧
      (∀ l, valid (comb (t l))) ∧
      ∀ i, ∑ l, w l * pay i (comb (t l)) = ∑ j, ∑ c, μ j c * f i j c := by sorry

end ExactAutobid.Equilibria
