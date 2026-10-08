-- Prove2me | Theorems.Thm_AlgebraicPCSP_Theory_lemma_4_11
-- name    : AlgebraicPCSP.Theory.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:28.225304+00:00
-- url     : https://prove2.me/theorems/530d0e15-e153-4ecd-8160-395735d857c5
-- title:
--   Lemma 4.11 — (A₂, F_M(A₂)) is a relaxation of a pp-power of (A₁, B₁), M = Pol(A₁, B₁)
-- statement:
--   Let $(\mathbf A_1,\mathbf B_1)$ be a PCSP template of finite structures, $\mathcal M=\mathrm{Pol}(\mathbf A_1,\mathbf B_1)$, and $\mathbf A_2$ a finite relational structure with nonempty relations (finite signatures, arities $\ge1$, nonempty finite domains). Then the template $(\mathbf A_2,F_{\mathcal M}(\mathbf A_2))$ is a relaxation of a pp-power of $(\mathbf A_1,\mathbf B_1)$: for some $N$ there is an $N$-th pp-power $(\mathbf A',\mathbf B')$ of $(\mathbf A_1,\mathbf B_1)$ in the signature of $\mathbf A_2$ and homomorphisms
--   $$h_A:\mathbf A_2\to\mathbf A',\qquad h_B:\mathbf B'\to F_{\mathcal M}(\mathbf A_2).$$
--
--   Combined with a homomorphism $F_{\mathcal M}(\mathbf A_2)\to\mathbf B_2$ this is the step (4) ⇒ (5) of Theorem 4.12. The free structure is built from fixed enumerations of $A_2$ and of the relations of $\mathbf A_2$.
--
--   **Formalization Note** The exponent $N$ is existentially quantified, as in the lemma ("a pp-power"); the proof uses $N=|A_1|^{|A_2|}$. Nonemptiness of $A_1$ and $A_2$ (the field's standing convention) is needed: for $A_2=\emptyset$ and nonempty $B_1$, a pp-power has a nonempty $B'$, which cannot map to the empty universe of $F_{\mathcal M}(\mathbf A_2)$. Every relation of $\mathbf A_2$ is also assumed nonempty, which the paper does not state but needs: if $R^{\mathbf A_2}=\emptyset$ then $R^{F_{\mathcal M}(\mathbf A_2)}=\emptyset$ (a minion has no nullary members), while for $\mathbf A_1=\mathbf B_1$ a one-point loop every pp-formula holds on $\mathbf B'$, so $R^{\mathbf B'}\neq\emptyset$ has nowhere to go and the lemma fails.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 26, Lemma 4.11

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

namespace AlgebraicPCSP.Theory

/-- Lemma 4.11 (arXiv:1811.00970v3, p. 26). Let `(𝔸₁, 𝔹₁)` be a PCSP template,
`M = Pol(𝔸₁, 𝔹₁)`, and `𝔸₂` a finite relational structure. Then the template `(𝔸₂, F_M(𝔸₂))` is a
relaxation of a pp-power of `(𝔸₁, 𝔹₁)`: for some `N` there is an `N`-th pp-power
`(𝔸', 𝔹')` of `(𝔸₁, 𝔹₁)`, in the signature of `𝔸₂`, of which `(𝔸₂, F_M(𝔸₂))` is a homomorphic
relaxation.

Every relation of `𝔸₂` is assumed nonempty (`hne`). The page does not say so, but without it the
lemma is false: for `𝔸₁ = 𝔹₁` a one-point loop and `𝔸₂` a one-point structure with an empty unary
relation `R`, `R^{F_M(𝔸₂)} = ∅` (minions have no nullary members), while every pp-formula holds on
the one-point loop, so `R^{𝔹'} ≠ ∅` cannot map into it. -/
theorem lemma_4_11 {τ₁ τ₂ : Type} [Fintype τ₁] [Fintype τ₂]
    {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} (har₁ : ∀ R, 0 < ar₁ R) (har₂ : ∀ R, 0 < ar₂ R)
    {A₁ B₁ A₂ : Type} [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype B₁] [DecidableEq B₁] [Nonempty B₁]
    [Fintype A₂] [DecidableEq A₂] [Nonempty A₂]
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁) (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁)
    (𝔸₂ : RelStruct τ₂ ar₂ A₂) (hne : ∀ R, (𝔸₂.rel R).Nonempty)
    {n : ℕ} (e : Fin n ≃ A₂) (m : τ₂ → ℕ) (eR : (R : τ₂) → Fin (m R) ≃ 𝔸₂.rel R) :
    ∃ (N : ℕ) (𝔸' : RelStruct τ₂ ar₂ (Fin N → A₁)) (𝔹' : RelStruct τ₂ ar₂ (Fin N → B₁)),
      IsPPPower N 𝔸₁ 𝔹₁ 𝔸' 𝔹' ∧
        IsRelaxation 𝔸' 𝔹' 𝔸₂ (freeStructure (Pol 𝔸₁ 𝔹₁ h₁) 𝔸₂ e m eR) := by sorry

end AlgebraicPCSP.Theory
