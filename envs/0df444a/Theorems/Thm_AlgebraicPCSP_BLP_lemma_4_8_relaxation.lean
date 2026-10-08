-- Prove2me | Theorems.Thm_AlgebraicPCSP_BLP_lemma_4_8_relaxation
-- name    : AlgebraicPCSP.BLP.lemma_4_8_relaxation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:35.148633+00:00
-- url     : https://prove2.me/theorems/6325784e-b162-48c0-8828-a8b35c5f13ee
-- title:
--   Lemma 4.8(1) for possibly infinite templates — a relaxation receives a minion homomorphism
-- statement:
--   Let $(\mathbf A_1,\mathbf B_1)$ and $(\mathbf A_2,\mathbf B_2)$ be two PCSP templates over the same finite signature with arities $\ge 1$; their domains may be infinite. If $(\mathbf A_2,\mathbf B_2)$ is a homomorphic relaxation of $(\mathbf A_1,\mathbf B_1)$, i.e. there are homomorphisms $h_A:\mathbf A_2\to\mathbf A_1$ and $h_B:\mathbf B_1\to\mathbf B_2$, then there is a minion homomorphism
--   $$\xi:\mathrm{Pol}(\mathbf A_1,\mathbf B_1)\to\mathrm{Pol}(\mathbf A_2,\mathbf B_2).$$
--
--   The paper proves Lemma 4.8 for finite templates and notes in the proof of Theorem 7.9 that the proof does not require finiteness; this version is the one used for the implication (4) ⇒ (3), where the templates live on powers of $\mathbb Q$.
--
--   **Formalization Note** Both pairs carry the template hypothesis, as in the lemma, which is what makes $\mathrm{Pol}$ a minion.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 25, Lemma 4.8(1); used for infinite structures on p. 48 (proof of Theorem 7.9)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_BLP_PPConstruction

namespace AlgebraicPCSP.BLP

open PCSPBLPAff.Symmetric

/-- Lemma 4.8(1) (arXiv:1811.00970v3, p. 25), for possibly infinite structures (p. 48: "the
proof does not require the structures to be finite"). Let `(𝔸₁, 𝔹₁)` and `(𝔸₂, 𝔹₂)` be two
similar PCSP templates over a finite signature. If `(𝔸₂, 𝔹₂)` is a (homomorphic) relaxation of
`(𝔸₁, 𝔹₁)`, then there is a minion homomorphism `ξ : AlgebraicPCSP.Theory.Pol(𝔸₁, 𝔹₁) → AlgebraicPCSP.Theory.Pol(𝔸₂, 𝔹₂)`. -/
theorem lemma_4_8_relaxation {τ : Type} [Finite τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A₁ B₁ A₂ B₂ : Type}
    (𝔸₁ : RelStruct τ ar A₁) (𝔹₁ : RelStruct τ ar B₁)
    (𝔸₂ : RelStruct τ ar A₂) (𝔹₂ : RelStruct τ ar B₂)
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    (hrel : AlgebraicPCSP.Theory.IsRelaxation 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    ∃ ξ, AlgebraicPCSP.Theory.IsMinionHom (AlgebraicPCSP.Theory.Pol 𝔸₁ 𝔹₁ h₁) (AlgebraicPCSP.Theory.Pol 𝔸₂ 𝔹₂ h₂) ξ := by sorry

end AlgebraicPCSP.BLP
