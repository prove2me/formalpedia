-- Prove2me | Theorems.Thm_CommonAgencyVCG_Algorithmic_claim_1
-- name    : CommonAgencyVCG.Algorithmic.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:31.367357+00:00
-- url     : https://prove2.me/theorems/86c8fa76-7f42-4a3f-8dba-061ad8f7ddca
-- title:
--   Claim 1, p. 17 — an IIVCG contract is IR iff E_{F|a*(b)}[t^ℓ(b,o)] ≤ m^ℓ(b) for all ℓ, b
-- statement:
--   Fix a common agency setting satisfying the standing assumptions, and for $\ell\in[n]$ and $b\in\mathcal V$ let
--   $$m^\ell(b) = \min_{\tilde v^\ell\in\mathcal V^\ell} \mathrm{Wel}^{a^*(b^{-\ell},\tilde v^\ell)}(b^{-\ell},\tilde v^\ell) - \mathrm{Wel}^{a^*(b)}(b^{-\ell},\mathbf 0).$$
--   An IIVCG contract $t$ satisfies individual rationality if and only if
--   $$\mathbb E_{o\sim F_{|a^*(b)}}[t^\ell(b,o)] \le m^\ell(b) \qquad \forall \ell\in[n],\ b\in\mathcal V.$$
--
--   The quantity $m^\ell(b)$ is thus the largest expected payment an IR IIVCG contract can extract from principal $\ell$.
--
--   **Formalization Note** The minimum is a real infimum over $\mathcal V^\ell$, which is nonempty and on which the welfare is bounded below.
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, p. 17, Claim 1

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

/-- Claim 1, p. 17: an IIVCG contract is IR iff `E_{o∼F|a*(b)}[t^ℓ(b, o)] ≤ m^ℓ(b)` for all
`ℓ` and `b ∈ V`. -/
theorem claim_1 (S : Setting n A O) (hS : S.Standing) (t : Contract n O) (ht : IsIIVCG S t) :
    IsIR S t ↔ ∀ ℓ b, InDom S b → E S (aStar S b) (t b ℓ) ≤ mBound S ℓ b := by sorry

end CommonAgencyVCG.Algorithmic
