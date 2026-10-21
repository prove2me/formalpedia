-- Prove2me | Theorems.Thm_CommonAgencyVCG_Algorithmic_claim_2
-- name    : CommonAgencyVCG.Algorithmic.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:38.619377+00:00
-- url     : https://prove2.me/theorems/cf48f552-78ee-49d2-aa79-6bd0f6459da3
-- title:
--   Claim 2, p. 18 — if an IIVCG contract is LL then k_{a*(b)} ≤ Σ_ℓ E_{F|a*(b)}[t^ℓ(b,o)]
-- statement:
--   Fix a common agency setting satisfying the standing assumptions, and for each action $a$ let $k_a = \min_{w\in\mathcal L_a}\mathbb E_{o\sim F_{|a}}[w(o)]$. If an IIVCG contract $t$ satisfies limited liability, then for every bid profile $b\in\mathcal V$
--   $$k_{a^*(b)} \le \sum_{\ell\in[n]} \mathbb E_{o\sim F_{|a^*(b)}}[t^\ell(b,o)].$$
--
--   Together with Claim 1 this gives the necessary condition $k_{a^*(b)} \le \sum_\ell m^\ell(b)$ of Lemma 2.
--
--   **Formalization Note** The minimum is a real infimum over $\mathcal L_a$; on $\mathcal L_{a^*(b)}$, which is nonempty, the expectation is bounded below by $0$.
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, p. 18, Claim 2

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

/-- Claim 2, p. 18: if an IIVCG contract is LL then
`k_{a*(b)} ≤ ∑_ℓ E_{o∼F|a*(b)}[t^ℓ(b, o)]` for all `b ∈ V`. -/
theorem claim_2 (S : Setting n A O) (hS : S.Standing) (t : Contract n O) (ht : IsIIVCG S t)
    (hLL : IsLL S t) (b : Fin n → O → ℝ) (hb : InDom S b) :
    kCost S (aStar S b) ≤ ∑ ℓ, E S (aStar S b) (t b ℓ) := by sorry

end CommonAgencyVCG.Algorithmic
