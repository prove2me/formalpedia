-- Prove2me | Theorems.Thm_CommonAgencyVCG_Algorithmic_claim_3
-- name    : CommonAgencyVCG.Algorithmic.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:45.298359+00:00
-- url     : https://prove2.me/theorems/cf646de8-a25d-4a76-8ad3-c960c73e4895
-- title:
--   Claim 3, p. 18 — if k_{a*(b)} ≤ Σ_ℓ m^ℓ(b) for all b, the Lemma 1 contract with h^ℓ = LP1 value and w^ℓ = x^b_ℓ w^b is IIVCG, LL, IR
-- statement:
--   Fix a common agency setting satisfying the standing assumptions, and suppose
--   $$k_{a^*(b)} \le \sum_{\ell\in[n]} m^\ell(b) \qquad \forall b\in\mathcal V.$$
--   Build a contract by Lemma 1's formula with
--
--   1. $h^\ell(b^{-\ell}) = \min_{\tilde v^\ell\in\mathcal V^\ell}\mathrm{Wel}^{a^*(b^{-\ell},\tilde v^\ell)}(b^{-\ell},\tilde v^\ell)$, and
--   2. for every $b\in\mathcal V$, $w^\ell = x^b_\ell\,w^b$, where $w^b\in\arg\min_{w\in\mathcal L_{a^*(b)}}\mathbb E_{o\sim F_{|a^*(b)}}[w(o)]$ and $0\le x^b_\ell$, $x^b_\ell\,k_{a^*(b)}\le m^\ell(b)$, $\sum_\ell x^b_\ell = 1$.
--
--   That is, $t^\ell(b,o) = h^\ell(b^{-\ell}) - \mathrm{Wel}^{a^*(b)}(b^{-\ell}, x^b_\ell w^b) + x^b_\ell\,w^b(o)$, the contract ALG1. For every such choice of $w^b$ and $x^b$, this contract is IIVCG and satisfies limited liability and individual rationality.
--
--   This is the constructive direction of Lemma 2.
--
--   **Formalization Note** Such choices of $w^b$ and $x^b$ exist. They are functions of $b$ subject to the stated conditions at every $b\in\mathcal V$ (`ValidSel`); the conclusion holds for all of them.
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, p. 18, Claim 3

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

/-- Claim 3, p. 18: if `k_{a*(b)} ≤ ∑_ℓ m^ℓ(b)` for all `b ∈ V`, admissible LP2/LP3
selections exist, and the contract of Lemma 1 with `h^ℓ` the LP1 value and
`w^ℓ = x^b_ℓ w^b` (any such selections) is IIVCG, LL and IR. -/
theorem claim_3 (S : Setting n A O) (hS : S.Standing)
    (hk : ∀ b, InDom S b → kCost S (aStar S b) ≤ ∑ ℓ, mBound S ℓ b) :
    (∃ (wsel : (Fin n → O → ℝ) → O → ℝ) (xsel : (Fin n → O → ℝ) → Fin n → ℝ),
      ValidSel S wsel xsel) ∧
    ∀ (wsel : (Fin n → O → ℝ) → O → ℝ) (xsel : (Fin n → O → ℝ) → Fin n → ℝ),
      ValidSel S wsel xsel →
        IsIIVCG S (alg1 S wsel xsel) ∧ IsLL S (alg1 S wsel xsel) ∧ IsIR S (alg1 S wsel xsel) := by sorry

end CommonAgencyVCG.Algorithmic
