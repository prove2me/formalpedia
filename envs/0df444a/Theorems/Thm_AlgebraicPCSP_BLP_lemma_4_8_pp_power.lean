-- Prove2me | Theorems.Thm_AlgebraicPCSP_BLP_lemma_4_8_pp_power
-- name    : AlgebraicPCSP.BLP.lemma_4_8_pp_power
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:12.023987+00:00
-- url     : https://prove2.me/theorems/a437dd8f-d2d8-4527-a607-1dea1b10f9c3
-- title:
--   Lemma 4.8(2) for possibly infinite templates — a pp-power receives a minion homomorphism
-- statement:
--   Let $(\mathbf A_1,\mathbf B_1)$ and $(\mathbf A_2,\mathbf B_2)$ be two PCSP templates over finite signatures with arities $\ge 1$; their domains may be infinite. If $(\mathbf A_2,\mathbf B_2)$ is an $n$-th pp-power of $(\mathbf A_1,\mathbf B_1)$, so that $A_2=A_1^n$, $B_2=B_1^n$ and every relation of the power is defined by one pp-formula over $(\mathbf A_1,\mathbf B_1)$, then there is a minion homomorphism
--   $$\xi:\mathrm{Pol}(\mathbf A_1,\mathbf B_1)\to\mathrm{Pol}(\mathbf A_2,\mathbf B_2).$$
--
--   Together with part (1), this gives a minion homomorphism along every pp-construction, which is the implication (4) ⇒ (3) of Theorem 7.9 for sequences starting at a finite reduct of $\mathbf Q_{\mathrm{conv}}$.
--
--   **Formalization Note** The domains of the power are literally `Fin n → A₁` and `Fin n → B₁`; the template hypothesis on the power is assumed, as in the lemma.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 25, Lemma 4.8(2); used for infinite structures on p. 48 (proof of Theorem 7.9)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_BLP_PPConstruction

namespace AlgebraicPCSP.BLP

open PCSPBLPAff.Symmetric

/-- Lemma 4.8(2) (arXiv:1811.00970v3, p. 25), for possibly infinite structures (p. 48: "the
proof does not require the structures to be finite"). Let `(𝔸₁, 𝔹₁)` and `(𝔸₂, 𝔹₂)` be two PCSP
templates over finite signatures. If `(𝔸₂, 𝔹₂)` is an `n`-th pp-power of `(𝔸₁, 𝔹₁)` (so
`A₂ = A₁ⁿ`, `B₂ = B₁ⁿ`), then there is a minion homomorphism `ξ : AlgebraicPCSP.Theory.Pol(𝔸₁, 𝔹₁) → AlgebraicPCSP.Theory.Pol(𝔸₂, 𝔹₂)`. -/
theorem lemma_4_8_pp_power {τ₁ τ₂ : Type} [Finite τ₁] [Finite τ₂]
    {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} (har₁ : ∀ R, 0 < ar₁ R) (har₂ : ∀ R, 0 < ar₂ R)
    {A₁ B₁ : Type} (n : ℕ)
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁)
    (𝔸₂ : RelStruct τ₂ ar₂ (Fin n → A₁)) (𝔹₂ : RelStruct τ₂ ar₂ (Fin n → B₁))
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    (hpow : AlgebraicPCSP.Theory.IsPPPower n 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    ∃ ξ, AlgebraicPCSP.Theory.IsMinionHom (AlgebraicPCSP.Theory.Pol 𝔸₁ 𝔹₁ h₁) (AlgebraicPCSP.Theory.Pol 𝔸₂ 𝔹₂ h₂) ξ := by sorry

end AlgebraicPCSP.BLP
