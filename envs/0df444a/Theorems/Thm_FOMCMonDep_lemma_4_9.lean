-- Prove2me | Theorems.Thm_FOMCMonDep_lemma_4_9
-- name    : FOMCMonDep.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:41.11635+00:00
-- url     : https://prove2.me/theorems/2c6041ff-b74a-4ca5-b159-d6518e9233ac
-- title:
--   Lemma 4.9 (Corollary of Gaifman locality) — $\mathrm{tp}^A_q(\bar a)$ depends only on $\mathrm{tp}^{A[B]}_{q'}(\bar a)$ for $B\supseteq\mathrm{Ball}^A_h(\bar a)$
-- statement:
--   For every $k,q,\alpha\in\mathbb N$ there are numbers $h=h(q)$ and $q'=q'(k,q,\alpha)$, computable from $k,q,\alpha$, with the following property. Let $\sigma$ be a finite relational signature of arity at most $\alpha$ and $A$ a $\sigma$-structure. For all $\bar a\in V(A)^k$ and $B\supseteq\mathrm{Ball}^A_h(\bar a)$, the type $\mathrm{tp}^A_q(\bar a)$ depends only on $\mathrm{tp}^{A[B]}_{q'}(\bar a)$: if $\bar a,\bar b\in V(A)^k$, $B_a\supseteq\mathrm{Ball}^A_h(\bar a)$, $B_b\supseteq\mathrm{Ball}^A_h(\bar b)$ and
--   $$\mathrm{tp}^{A[B_a]}_{q'}(\bar a)=\mathrm{tp}^{A[B_b]}_{q'}(\bar b),\qquad\text{then}\qquad \mathrm{tp}^A_q(\bar a)=\mathrm{tp}^A_q(\bar b).$$
--   The numbers $h$ and $q'$ do not depend on the signature.
--
--   This is the locality tool behind Lemma 4.10 and Lemma 6.1.
--
--   **Formalization Note** Balls are in the Gaifman graph of $A$; the signature is relational, has finitely many symbols, none of arity above $\alpha$; the structure may be infinite. Computability is Mathlib's `Computable`.
--
--   Differences from the source:
--   - reading: tp^A_q(ā) depends only on tp^{A[B]}_{q′}(ā) → for all ā, b̄ and B_a ⊇ Ball_h(ā), B_b ⊇ Ball_h(b̄): equal q′-types in A[B_a] and A[B_b] imply equal q-types in A; reason: the meaning used in the proof (App. B, p.61); the strongest reading
--   - encoding: computable from k, q, α → Mathlib Computable h and Computable of (k, q, α) ↦ q′ k q α; reason: Mathlib's notion of computability on ℕ
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Lemma 4.9, p.15 (PDF 17)

import Mathlib
import Definitions.Def_FOMCMonDep_tp
import Definitions.Def_FOMCMonDep_gaifman

set_option autoImplicit false

open FirstOrder FirstOrder.Language

universe u v w

namespace FOMCMonDep

/-- **Lemma 4.9 (Corollary of Gaifman locality).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §4.1.3, p.15 (PDF 17); proof App. B,
p.61 (PDF 63): "For every k, q, α ∈ N, there are numbers h = h(q) and q′ = q′(k, q, α) computable from k, q, α, with
the following property. Fix a finite relational signature σ of arity at most α and a σ-structure A. Then, for all
ā ∈ V(A)^k and B ⊇ Ball^A_h(ā), tp^A_q(ā) depends only on tp^{A[B]}_{q′}(ā)."

**Formalization Note.** "depends only on" is stated as the paper's proof uses it: for tuples `ā, b̄` and sets
`B_a ⊇ Ball^A_h(ā)`, `B_b ⊇ Ball^A_h(b̄)`, equal `q′`-types in `A[B_a]` and `A[B_b]` give equal `q`-types in `A`. The
tuples are given in `B_a`, `B_b` (they lie in their own balls). `h` is a function of `q` alone and `q′` of
`(k, q, α)`; both are Mathlib-`Computable`, and they are chosen before the signature, so they do not depend on it
(p.62: "we crucially use that h and q′ do not depend on the signature"). The signature is relational
(`IsRelational`), has finitely many relation symbols, and none of arity above `α`; the structure `A` (any carrier,
possibly infinite) is `S`. Balls are in the Gaifman graph `gaifman S`, distances in `ℕ∞`. Types are
parameter-free (`tp0`). -/
theorem lemma_4_9 :
    ∃ (h : ℕ → ℕ) (q' : ℕ → ℕ → ℕ → ℕ), Computable h ∧
      Computable (fun p : ℕ × ℕ × ℕ => q' p.1 p.2.1 p.2.2) ∧
      ∀ (k q α : ℕ) (L : FirstOrder.Language.{u, v}) [L.IsRelational] [Finite (Σ l, L.Relations l)],
        (∀ l, α < l → IsEmpty (L.Relations l)) →
        ∀ (M : Type w) (S : L.Structure M) (Ba Bb : Set M) (a : Fin k → Ba) (b : Fin k → Bb),
          {x | ∃ i, (gaifman S).edist (a i : M) x ≤ (h q : ℕ∞)} ⊆ Ba →
          {x | ∃ i, (gaifman S).edist (b i : M) x ≤ (h q : ℕ∞)} ⊆ Bb →
          tp0 (inducedStructure S Ba) (q' k q α) a = tp0 (inducedStructure S Bb) (q' k q α) b →
          tp0 S q (fun i => (a i : M)) = tp0 S q (fun i => (b i : M)) := by sorry

end FOMCMonDep
