-- Prove2me | Theorems.Thm_FOMCMonDep_theorem_4_4
-- name    : FOMCMonDep.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:46.234231+00:00
-- url     : https://prove2.me/theorems/eec53217-c965-4cc3-a38b-6f05e64a5c24
-- title:
--   Theorem 4.4 — $|\mathrm{Types}^{G^+}_{k,q}(V(G)/U)|\le O_{\mathcal C,q,k,c}(1)\cdot\mathrm{poly}_{\mathcal C,q,k}(|U|)$
-- statement:
--   Let $\mathcal C$ be a monadically dependent class of (possibly infinite) graphs and $k,q,c\in\mathbb N$. For every $G\in\mathcal C$, every expansion $G^+$ of $G$ by $c$ unary predicates and every finite $U\subseteq V(G)$,
--   $$\bigl|\mathrm{Types}^{G^+}_{k,q}(V(G)/U)\bigr|\le O_{\mathcal C,q,k,c}(1)\cdot\mathrm{poly}_{\mathcal C,q,k}(|U|).$$
--   The number $c$ of unary predicates affects only the constant factor, not the degree of the polynomial.
--
--   This is the type bound of Part I, an extension of the Sauer–Shelah lemma to higher quantifier rank in monadically dependent classes. It bounds the depth-$q$ width of definable construction sequences (Lemma 4.10).
--
--   **Formalization Note** The bound is $A\,(|U|+2)^D$ with $D$ chosen after $\mathcal C,q,k$ and before $c$, and $A$ chosen after $c$. The number of types is an extended natural number, so the bound also says it is finite.
--
--   Differences from the source:
--   - encoding: a monadically dependent class of possibly infinite graphs (Part I) → AnyGraphClass (members on every vertex type) with MonDepAny; reason: the paper's definition with the witness graph on any type; Part I allows infinite graphs
--   - encoding: formulas with parameters from U (constants) → formulas whose extra free variables range over U, each assigned itself; reason: same satisfying tuples and quantifier rank, hence the same number of types
--   - encoding: O_{C,q,k,c}(1) · poly_{C,q,k}(|U|) → A · (|U| + 2)^D, D before c and A after c; reason: the asymptotic convention of §3, p.11
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 4.4, p.17 (PDF 19)

import Mathlib
import Definitions.Def_FOMCMonDep_tp
import Definitions.Def_FOMCMonDep_MonDepAny

set_option autoImplicit false

namespace FOMCMonDep

/-- **Theorem 4.4.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), Part I, p.17 (PDF 19); first printed for finite graphs p.14 (PDF 16),
proof p.27 (PDF 29): "Let 𝒞 be a monadically dependent graph class and k, q, c ∈ N. For every (possibly infinite) graph
G ∈ 𝒞, expansion G⁺ of G by c unary predicates, and finite subset U ⊆ V(G),
|Types^{G⁺}_{k,q}(V(G)/U)| ⩽ O_{𝒞,q,k,c}(1) · poly_{𝒞,q,k}(|U|)."
p.14: "The number c of unary predicates affects only the constant factor, not the degree of the polynomial."

**Formalization Note.** `O_{𝒞,q,k,c}(1) · poly_{𝒞,q,k}(|U|)` is `A · (|U| + 2)^D` (§3, p.11: "g(n) ⩽ poly_k(n) has
the same implications as g(n) ⩽ (n + 2)^{O_k(1)}"), with the degree `D` chosen after `𝒞, q, k` and **before** `c`,
and the factor `A` after `c`. The expansion `G⁺` is the published `MonDepMW.coloredStructure G col` with `c`
predicates. Part I (possibly infinite graphs, `AnyGraphClass`, `MonDepAny`); the count is an `encard`, so the bound
also asserts finiteness. -/
theorem theorem_4_4 (𝒞 : AnyGraphClass) (h𝒞 : MonDepAny 𝒞) (k q : ℕ) :
    ∃ D : ℕ, ∀ c : ℕ, ∃ A : ℕ, ∀ (V : Type) (G : SimpleGraph V), G ∈ 𝒞 V →
      ∀ (col : Fin c → Set V) (U : Set V), U.Finite →
        typeCount (MonDepMW.coloredStructure G col) k q Set.univ U ≤ ((A * (U.ncard + 2) ^ D : ℕ) : ℕ∞) := by sorry

end FOMCMonDep
