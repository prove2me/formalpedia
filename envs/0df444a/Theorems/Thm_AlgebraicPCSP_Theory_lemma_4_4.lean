-- Prove2me | Theorems.Thm_AlgebraicPCSP_Theory_lemma_4_4
-- name    : AlgebraicPCSP.Theory.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:47.205377+00:00
-- url     : https://prove2.me/theorems/c8b3b5d2-49e5-4b64-83b2-cc0267452466
-- title:
--   Lemma 4.4 — homomorphisms F_M(A) → B correspond one-to-one to minion homomorphisms M → Pol(A, B)
-- statement:
--   Let $\mathcal M$ be a minion on a pair of finite sets and $(\mathbf A,\mathbf B)$ a PCSP template of finite structures (finite signature, arities $\ge1$, nonempty finite domains), with a fixed enumeration $A=\{a_1,\dots,a_n\}$ and fixed enumerations of the relations $R^{\mathbf A}$. There is a one-to-one correspondence
--   $$\{c: F_{\mathcal M}(\mathbf A)\to\mathbf B\text{ homomorphism}\}\ \longleftrightarrow\ \{\xi:\mathcal M\to\mathrm{Pol}(\mathbf A,\mathbf B)\text{ minion homomorphism}\},$$
--   under which a minion homomorphism $\xi$ corresponds to the homomorphism
--   $$c_\xi: f\mapsto \xi(f)(a_1,\dots,a_n)\qquad (f\in\mathcal M^{(n)}).$$
--
--   The lemma says that the free structure is the most general structure receiving a minion homomorphism from $\mathcal M$: deciding whether $\mathcal M\to\mathrm{Pol}(\mathbf A,\mathbf B)$ reduces to a homomorphism question between finite structures.
--
--   **Formalization Note** The correspondence is stated as an explicit equivalence between the subtype of homomorphisms and the subtype of minion homomorphisms (maps defined on the members of $\mathcal M$), whose inverse sends $\xi$ to $c_\xi$; the tuple $(a_1,\dots,a_n)$ is the enumeration $e$ itself. This is an extra item: the proof of Theorem 4.12 does not cite it.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 24, Lemma 4.4 (the map c_ξ from its proof, p. 24)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

namespace AlgebraicPCSP.Theory

/-- Lemma 4.4 (arXiv:1811.00970v3, p. 24). Let `M` be a minion (on finite sets) and `(𝔸, 𝔹)` a
PCSP template. There is a one-to-one correspondence between homomorphisms `c : F_M(𝔸) → 𝔹` and
minion homomorphisms `ξ : M → Pol(𝔸, 𝔹)`; the minion homomorphism `ξ` corresponds to
`c_ξ : f ↦ ξ(f)(a₁, …, aₙ)`, where `a_i = e i` is the enumeration of `A` (p. 24). -/
theorem lemma_4_4 {C D : Type} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (M : Minion C D) {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (h : IsPromiseTemplate 𝔸 𝔹)
    {n : ℕ} (e : Fin n ≃ A) (m : τ → ℕ) (eR : (R : τ) → Fin (m R) ≃ 𝔸.rel R) :
    ∃ Φ : {c : {f // f ∈ M.mem n} → B // IsHom (freeStructure M 𝔸 e m eR) 𝔹 c} ≃
        {ξ : (k : ℕ) → {f // f ∈ M.mem k} → {f // f ∈ (Pol 𝔸 𝔹 h).mem k} //
          IsMinionHom M (Pol 𝔸 𝔹 h) ξ},
      ∀ ξ, (Φ.symm ξ).val = fun f => (ξ.val n f).val e := by sorry

end AlgebraicPCSP.Theory
