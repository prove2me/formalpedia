-- Prove2me | Theorems.Thm_CommonAgencyVCG_Algorithmic_lemma_1
-- name    : CommonAgencyVCG.Algorithmic.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:32.661279+00:00
-- url     : https://prove2.me/theorems/ac8be80a-f78f-4b47-bef2-defa84e46777
-- title:
--   Lemma 1, p. 13 — t is IIVCG iff t^ℓ(b,o) = h^ℓ(b^{−ℓ}) − Wel^{a*(b)}(b^{−ℓ}, w^ℓ) + w^ℓ(o) with Σ_ℓ w^ℓ ∈ L_{a*(b)}
-- statement:
--   This is the outcome-specific payment characterization of IIVCG contracts.
--
--   Fix a common agency setting satisfying the standing assumptions, and let $t$ be a contract. Then $t$ is IIVCG if and only if there exist functions $h^1,\dots,h^n$, with $h^\ell$ depending only on the bids $b^{-\ell}$ of the other principals, such that for every bid profile $b\in\mathcal V$ there are vectors $w^1,\dots,w^n\in\mathbb R^m_{\ge 0}$ with $\sum_\ell w^\ell \in \mathcal L_{a^*(b)}$ and
--   $$t^\ell(b,o) = h^\ell(b^{-\ell}) - \mathrm{Wel}^{a^*(b)}(b^{-\ell}, w^\ell) + w^\ell(o) \qquad \forall \ell\in[n],\ o\in\mathcal O.$$
--
--   Definition 2 constrains only expected payments; this lemma turns it into an explicit outcome-by-outcome form, which is what the construction of ALG1 instantiates.
--
--   **Formalization Note** $h^\ell$ is a function of the whole profile that is invariant under changes of coordinate $\ell$. Appendix B.2 writes $\mathrm{Wel}^{a^*(b)}(b^{\ell}, w^\ell)$ where $(b^{-\ell}, w^\ell)$ is meant; the statement follows p. 13.
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, p. 13, Lemma 1 (proof: Appendix B.2, p. 32)

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

/-- Lemma 1, p. 13 (outcome-specific payment characterization). -/
theorem lemma_1 (S : Setting n A O) (hS : S.Standing) (t : Contract n O) :
    IsIIVCG S t ↔
      ∃ h : Fin n → (Fin n → O → ℝ) → ℝ,
        (∀ ℓ b b', (∀ k, k ≠ ℓ → b k = b' k) → h ℓ b = h ℓ b') ∧
          ∀ b, InDom S b → ∃ w : Fin n → O → ℝ, (∀ ℓ o, 0 ≤ w ℓ o) ∧
            (∑ ℓ, w ℓ) ∈ implSet S (aStar S b) ∧
              ∀ ℓ o, t b ℓ o = h ℓ b - Wel S (aStar S b) (Function.update b ℓ (w ℓ)) + w ℓ o := by sorry

end CommonAgencyVCG.Algorithmic
