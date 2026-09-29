-- Prove2me | Theorems.Thm_Diaz_exists_ringHom_of_transcendental
-- name    : Diaz.exists_ringHom_of_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:21:20.434512+00:00
-- url     : https://prove2.me/theorems/7bbf5261-1a2e-4517-86c7-6a029b955652
-- title:
--   Steinitz extension: a ring endomorphism of $\mathbb{C}$ fixing $K$ and moving one transcendental to another
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and let $u, t \in \mathbb{C}$ both be **transcendental over $K$**, that is, neither is a root of a non-zero polynomial with coefficients in $K$. Then
--
--   $$\exists\, \Phi : \mathbb{C} \to \mathbb{C} \ \text{a ring homomorphism, with } \Phi|_{K} = \mathrm{id}_{K} \ \text{ and } \ \Phi(u) = t.$$
--
--   Here $\Phi$ ranges over ring homomorphisms $\mathbb{C} \to \mathbb{C}$ (`ℂ →+* ℂ`), "$\Phi$ fixes $K$ pointwise" is $\forall a \in K,\ \Phi(a) = a$, and no continuity is asked for.
--
--   **Why it is true.** Since $u$ and $t$ are both transcendental over $K$, the simple extensions $K(u)$ and $K(t)$ are each $K$-isomorphic to the rational function field $K(X)$, so $u \mapsto t$ extends to an isomorphism $K(u) \to K(t)$ fixing $K$. A transcendence basis of $\mathbb{C}$ over $K(u)$ and one over $K(t)$ both have the cardinality of the continuum, so they may be matched; extending algebraically is possible because $\mathbb{C}$ is algebraically closed. See Lang, *Algebra*, 3rd ed., Ch. VIII, or any account of Steinitz's theorem.
--
--   **Where the difficulty sits.** Mathlib carries the ingredients — `IsAlgClosed.equivOfTranscendenceBasis` matches two algebraically closed fields along a bijection of transcendence bases, and `IsAlgClosed.lift` extends an embedding into an algebraically closed field — but not the assembled statement, and the assembly is the work: one must produce the $K$-isomorphism $K(u) \cong K(t)$, promote it along transcendence bases of $\mathbb{C}$ over each of the two, and check the cardinality bookkeeping. There is no known obstruction; this is a formalisation task, not an open problem.
--
--   **Deliberate weaknesses in the thesis.** Only a ring *endomorphism* is asked for, not an automorphism — that is all the downstream results consume, and an endomorphism of a field is automatically injective. The transcendence hypothesis is necessary rather than decorative: if $u$ is algebraic over $K$ and $t$ is not, no such map exists.
--
--   **Role.** This node replaces what the source project declares as an `axiom`. It is the existence half of the closure theorem for Diaz's modulus conjecture: it is what upgrades the conditional statement "*an isomorphism matching the generators intertwines conjugation*" into the unconditional "*a candidate counterexample and an ordinary point of the same circle are carried onto one another*". Publishing it as a node rather than assuming it keeps the assumed surface of the development visible and provable.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Axioms.lean#L41-L61

import Mathlib

theorem Diaz.exists_ringHom_of_transcendental {K : Subfield ℂ} {u t : ℂ}
    (hu : Transcendental (↥K) u) (ht : Transcendental (↥K) t) :
    ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t := by sorry
