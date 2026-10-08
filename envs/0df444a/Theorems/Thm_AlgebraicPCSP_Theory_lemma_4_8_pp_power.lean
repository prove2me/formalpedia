-- Prove2me | Theorems.Thm_AlgebraicPCSP_Theory_lemma_4_8_pp_power
-- name    : AlgebraicPCSP.Theory.lemma_4_8_pp_power
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:39.511092+00:00
-- url     : https://prove2.me/theorems/a84d24d8-5105-4784-8a06-b93fb238ba4b
-- title:
--   Lemma 4.8(2) — a pp-power (A₂, B₂) of (A₁, B₁) gives a minion homomorphism Pol(A₁, B₁) → Pol(A₂, B₂)
-- statement:
--   Let $(\mathbf A_1,\mathbf B_1)$ be a PCSP template of finite structures and let $(\mathbf A_2,\mathbf B_2)$, with $A_2=A_1^n$ and $B_2=B_1^n$, be a PCSP template that is an $n$-th pp-power of $(\mathbf A_1,\mathbf B_1)$ (Definition 4.7); both signatures are finite with arities $\ge1$. Then there is a minion homomorphism
--   $$\xi:\mathrm{Pol}(\mathbf A_1,\mathbf B_1)\to\mathrm{Pol}(\mathbf A_2,\mathbf B_2).$$
--
--   Together with part (1) this gives Corollary 4.10 and the step (6) ⇒ (1) of Theorem 4.12.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 25, Lemma 4.8(2)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

namespace AlgebraicPCSP.Theory

/-- Lemma 4.8(2) (arXiv:1811.00970v3, p. 25). Let `(𝔸₁, 𝔹₁)` and `(𝔸₂, 𝔹₂)` be two PCSP
templates. If `(𝔸₂, 𝔹₂)` is an `n`-th pp-power of `(𝔸₁, 𝔹₁)` (so `A₂ = A₁ⁿ`, `B₂ = B₁ⁿ`), then
there is a minion homomorphism `ξ : Pol(𝔸₁, 𝔹₁) → Pol(𝔸₂, 𝔹₂)`. -/
theorem lemma_4_8_pp_power {τ₁ τ₂ : Type} [Fintype τ₁] [Fintype τ₂]
    {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} (har₁ : ∀ R, 0 < ar₁ R) (har₂ : ∀ R, 0 < ar₂ R)
    {A₁ B₁ : Type} [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype B₁] [DecidableEq B₁] [Nonempty B₁] (n : ℕ)
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁)
    (𝔸₂ : RelStruct τ₂ ar₂ (Fin n → A₁)) (𝔹₂ : RelStruct τ₂ ar₂ (Fin n → B₁))
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    (hpow : IsPPPower n 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    ∃ ξ, IsMinionHom (Pol 𝔸₁ 𝔹₁ h₁) (Pol 𝔸₂ 𝔹₂ h₂) ξ := by sorry

end AlgebraicPCSP.Theory
