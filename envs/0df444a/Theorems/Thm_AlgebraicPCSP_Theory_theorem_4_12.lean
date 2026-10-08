-- Prove2me | Theorems.Thm_AlgebraicPCSP_Theory_theorem_4_12
-- name    : AlgebraicPCSP.Theory.theorem_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:36.492853+00:00
-- url     : https://prove2.me/theorems/0082bade-7c1a-46b5-9a1a-eaa17b7887ed
-- title:
--   Theorem 4.12 — a minion homomorphism Pol(A₁, B₁) → Pol(A₂, B₂) exists iff (A₂, B₂) is pp-constructible from (A₁, B₁), and four other equivalent conditions
-- statement:
--   Let $(\mathbf A_1,\mathbf B_1)$ and $(\mathbf A_2,\mathbf B_2)$ be PCSP templates of finite structures (finite signatures, arities $\ge1$, nonempty finite domains, every relation of $\mathbf A_2$ nonempty), and let $\mathcal M_i=\mathrm{Pol}(\mathbf A_i,\mathbf B_i)$. Fix an enumeration of $A_2$ and of each relation of $\mathbf A_2$, used to build $\Sigma(\mathbf A_2,\cdot)$ and the free structure $F_{\mathcal M_1}(\mathbf A_2)$. The following are equivalent:
--
--   1. there exists a minion homomorphism $\xi:\mathcal M_1\to\mathcal M_2$;
--   2. $\mathcal M_2$ satisfies all bipartite minor conditions satisfied in $\mathcal M_1$;
--   3. $\mathcal M_2$ satisfies the condition $\Sigma(\mathbf A_2,F_{\mathcal M_1}(\mathbf A_2))$;
--   4. there exists a homomorphism from $F_{\mathcal M_1}(\mathbf A_2)$ to $\mathbf B_2$;
--   5. $(\mathbf A_2,\mathbf B_2)$ is a homomorphic relaxation of a pp-power of $(\mathbf A_1,\mathbf B_1)$;
--   6. $(\mathbf A_2,\mathbf B_2)$ is pp-constructible from $(\mathbf A_1,\mathbf B_1)$.
--
--   Schematically,
--   $$\mathcal M_1\to\mathcal M_2\iff F_{\mathcal M_1}(\mathbf A_2)\to\mathbf B_2\iff(\mathbf A_2,\mathbf B_2)\text{ is pp-constructible from }(\mathbf A_1,\mathbf B_1).$$
--
--   The theorem makes the existence of a minion homomorphism, a property of infinitely many polymorphisms, equivalent to a homomorphism between two finite structures and to a relational construction. Combined with Theorem 3.1 of the paper it gives a log-space reduction from $\mathrm{PCSP}(\mathbf A_2,\mathbf B_2)$ to $\mathrm{PCSP}(\mathbf A_1,\mathbf B_1)$ in each of these cases.
--
--   **Formalization Note** All four domains are assumed nonempty, the field's standing convention for relational structures (the paper's proof takes $A_2=[n]$). Without it the statement fails: for $A_2=\emptyset$, item (4) holds trivially while item (5) can fail. Every relation of $\mathbf A_2$ is also assumed nonempty. The paper does not state this either, but (4) ⇒ (5) fails without it: for $\mathbf A_1=\mathbf B_1$ a one-point loop and $\mathbf A_2=\mathbf B_2$ a one-point structure with an empty unary relation, items (1)–(4) hold, while every pp-power of the loop has a nonempty relation on its one-point $\mathbf B'$, which cannot map into the empty relation of $\mathbf B_2$. The conclusion is `List.TFAE` of the six conditions. In (2) the quantifier ranges over all bipartite minor conditions whose symbol and identity sets are finite types in `Type`. (5) asks for some $N$, an $N$-th pp-power $(\mathbf A',\mathbf B')$ of $(\mathbf A_1,\mathbf B_1)$ in the signature of $\mathbf A_2$, and homomorphisms $\mathbf A_2\to\mathbf A'$ and $\mathbf B'\to\mathbf B_2$. (6) is stated between the bundled templates.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 27, Theorem 4.12

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

namespace AlgebraicPCSP.Theory

/-- Theorem 4.12 (arXiv:1811.00970v3, p. 27). Let `(𝔸ᵢ, 𝔹ᵢ)`, `i = 1, 2`, be (finite) PCSP
templates and `Mᵢ = Pol(𝔸ᵢ, 𝔹ᵢ)`. The following are equivalent:
(1) there exists a minion homomorphism `ξ : M₁ → M₂`;
(2) `M₂` satisfies all bipartite minor conditions satisfied in `M₁`;
(3) `M₂` satisfies the condition `Σ(𝔸₂, F_{M₁}(𝔸₂))`;
(4) there exists a homomorphism from `F_{M₁}(𝔸₂)` to `𝔹₂`;
(5) `(𝔸₂, 𝔹₂)` is a homomorphic relaxation of a pp-power of `(𝔸₁, 𝔹₁)`;
(6) `(𝔸₂, 𝔹₂)` is pp-constructible from `(𝔸₁, 𝔹₁)`.
`Σ(𝔸₂, ·)` and `F_{M₁}(𝔸₂)` are built from the enumeration `e` of `A₂` and the enumerations
`eR R` of the relations `R^{𝔸₂}`.

Every relation of `𝔸₂` is assumed nonempty (`hne`). The page does not say so, but without it
(4) ⇒ (5) fails: for `𝔸₁ = 𝔹₁` a one-point loop and `𝔸₂ = 𝔹₂` a one-point structure with an empty
unary relation, (1)–(4) hold, while every pp-power of the loop has a nonempty relation on its one
point `𝔹'`, which cannot map into the empty relation of `𝔹₂`. -/
theorem theorem_4_12 {τ₁ τ₂ : Type} [Fintype τ₁] [Fintype τ₂]
    {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} (har₁ : ∀ R, 0 < ar₁ R) (har₂ : ∀ R, 0 < ar₂ R)
    {A₁ B₁ A₂ B₂ : Type} [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype B₁] [DecidableEq B₁] [Nonempty B₁]
    [Fintype A₂] [DecidableEq A₂] [Nonempty A₂] [Fintype B₂] [DecidableEq B₂] [Nonempty B₂]
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁)
    (𝔸₂ : RelStruct τ₂ ar₂ A₂) (𝔹₂ : RelStruct τ₂ ar₂ B₂) (hne : ∀ R, (𝔸₂.rel R).Nonempty)
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    {n : ℕ} (e : Fin n ≃ A₂) (m : τ₂ → ℕ) (eR : (R : τ₂) → Fin (m R) ≃ 𝔸₂.rel R) :
    List.TFAE
      [ ∃ ξ, IsMinionHom (Pol 𝔸₁ 𝔹₁ h₁) (Pol 𝔸₂ 𝔹₂ h₂) ξ,
        ∀ S : BipartiteMinorCondition, (Pol 𝔸₁ 𝔹₁ h₁).Satisfies S → (Pol 𝔸₂ 𝔹₂ h₂).Satisfies S,
        (Pol 𝔸₂ 𝔹₂ h₂).Satisfies
          (sigmaCondition 𝔸₂ (freeStructure (Pol 𝔸₁ 𝔹₁ h₁) 𝔸₂ e m eR) e m eR),
        ∃ c, IsHom (freeStructure (Pol 𝔸₁ 𝔹₁ h₁) 𝔸₂ e m eR) 𝔹₂ c,
        ∃ (N : ℕ) (𝔸' : RelStruct τ₂ ar₂ (Fin N → A₁)) (𝔹' : RelStruct τ₂ ar₂ (Fin N → B₁)),
          IsPPPower N 𝔸₁ 𝔹₁ 𝔸' 𝔹' ∧ IsRelaxation 𝔸' 𝔹' 𝔸₂ 𝔹₂,
        PPConstructible (Template.of 𝔸₁ 𝔹₁ har₁) (Template.of 𝔸₂ 𝔹₂ har₂) ] := by sorry

end AlgebraicPCSP.Theory
