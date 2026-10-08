-- Prove2me | Theorems.Thm_AlgebraicPCSP_Theory_lemma_4_8_relaxation
-- name    : AlgebraicPCSP.Theory.lemma_4_8_relaxation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:04.058+00:00
-- url     : https://prove2.me/theorems/5842bcf0-77f8-4b68-a2d4-b005e1ff644f
-- title:
--   Lemma 4.8(1) — a relaxation (A₂, B₂) of (A₁, B₁) gives a minion homomorphism Pol(A₁, B₁) → Pol(A₂, B₂)
-- statement:
--   Let $(\mathbf A_1,\mathbf B_1)$ and $(\mathbf A_2,\mathbf B_2)$ be two similar PCSP templates of finite structures (finite signature, arities $\ge1$, nonempty finite domains). If $(\mathbf A_2,\mathbf B_2)$ is a homomorphic relaxation of $(\mathbf A_1,\mathbf B_1)$, i.e. there are homomorphisms $h_A:\mathbf A_2\to\mathbf A_1$ and $h_B:\mathbf B_1\to\mathbf B_2$, then there is a minion homomorphism
--   $$\xi:\mathrm{Pol}(\mathbf A_1,\mathbf B_1)\to\mathrm{Pol}(\mathbf A_2,\mathbf B_2).$$
--
--   Together with part (2) this gives Corollary 4.10 and the step (6) ⇒ (1) of Theorem 4.12.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 25, Lemma 4.8(1)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

namespace AlgebraicPCSP.Theory

/-- Lemma 4.8(1) (arXiv:1811.00970v3, p. 25). Let `(𝔸₁, 𝔹₁)` and `(𝔸₂, 𝔹₂)` be two similar PCSP
templates. If `(𝔸₂, 𝔹₂)` is a (homomorphic) relaxation of `(𝔸₁, 𝔹₁)`, then there is a minion
homomorphism `ξ : Pol(𝔸₁, 𝔹₁) → Pol(𝔸₂, 𝔹₂)`. -/
theorem lemma_4_8_relaxation {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A₁ B₁ A₂ B₂ : Type} [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype B₁] [DecidableEq B₁] [Nonempty B₁]
    [Fintype A₂] [DecidableEq A₂] [Nonempty A₂] [Fintype B₂] [DecidableEq B₂] [Nonempty B₂]
    (𝔸₁ : RelStruct τ ar A₁) (𝔹₁ : RelStruct τ ar B₁)
    (𝔸₂ : RelStruct τ ar A₂) (𝔹₂ : RelStruct τ ar B₂)
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    (hrel : IsRelaxation 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    ∃ ξ, IsMinionHom (Pol 𝔸₁ 𝔹₁ h₁) (Pol 𝔸₂ 𝔹₂ h₂) ξ := by sorry

end AlgebraicPCSP.Theory
