-- Prove2me | Theorems.Thm_FiniteField_artinSchreier_translate_invariants_algEquiv_and_isGaloisGroup
-- name    : FiniteField.artinSchreier_translate_invariants_algEquiv_and_isGaloisGroup
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:25:40.84437+00:00
-- url     : https://prove2.me/theorems/2f12de1f-aa2f-4094-936b-41368b483590
-- title:
--   Artin-Schreier cover of the affine line: translation-invariant polynomials over F_q are the polynomials in X^q - X, and F_q[X] is Galois over them with group (F_q, +) and trivial inertia
-- statement:
--   Let $\mathbb{F}_q$ be a finite field with $q$ elements and let the additive group $(\mathbb{F}_q, +)$ act on the polynomial ring $\mathbb{F}_q[X]$ by translations,
--
--   $$c \cdot p(X) = p(X + c) \qquad (c \in \mathbb{F}_q,\ p \in \mathbb{F}_q[X]),$$
--
--   an action by $\mathbb{F}_q$-algebra automorphisms. Let $\mathbb{F}_q[X]^{\mathbb{F}_q} = \{p : p(X + c) = p(X) \text{ for all } c \in \mathbb{F}_q\}$ be the invariant subalgebra. Then:
--
--   1. **The invariants form a polynomial ring in $X^q - X$**: the map $g(T) \mapsto g(X^q - X)$ is an isomorphism of $\mathbb{F}_q$-algebras
--
--   $$\mathbb{F}_q[T] \xrightarrow{\ \sim\ } \mathbb{F}_q[X]^{\mathbb{F}_q}.$$
--
--      That is, a polynomial is invariant under every translation $X \mapsto X + c$ if and only if it is of the form $g(X^q - X)$, and then $g$ is unique.
--   2. **Galois**: the action is faithful and its ring of invariants is $\mathbb{F}_q[X]^{\mathbb{F}_q}$, so $(\mathbb{F}_q, +)$ is a Galois group of the ring extension $\mathbb{F}_q[X] / \mathbb{F}_q[X]^{\mathbb{F}_q}$.
--   3. **Finite**: $\mathbb{F}_q[X]$ is a finitely generated module over $\mathbb{F}_q[X]^{\mathbb{F}_q}$.
--   4. **Unramified**: for every prime ideal $Q$ of $\mathbb{F}_q[X]$ the inertia group $\{c : p(X + c) - p(X) \in Q \text{ for all } p\}$ is trivial.
--
--   Geometrically, $x \mapsto x^q - x$ is the quotient map $\mathbb{A}^1 \to \mathbb{A}^1 / \mathbb{F}_q \cong \mathbb{A}^1$, a finite etale Galois cover with group $\mathbb{F}_q$ (the Artin-Schreier cover used to build the Artin-Schreier sheaves $\mathcal{L}_\psi$). The proof: $X^q - X = \prod_{c \in \mathbb{F}_q}(X - c)$ is translation invariant; an invariant $p$ takes the value $p(0)$ at every $c \in \mathbb{F}_q$, so $X^q - X$ divides $p - p(0)$ and the quotient is again invariant of smaller degree, which gives $p = g(X^q - X)$ by induction; $g \mapsto g(X^q - X)$ is injective since $X^q - X$ is not constant. Finiteness follows from integrality over the invariants, and the inertia is trivial because $c \cdot X - X = c$ is a unit for $c \neq 0$.
--
--   **Formalization Note**: the group is `Multiplicative Fq` (the additive group of $\mathbb{F}_q$ written multiplicatively, as Mathlib's group actions require). The translation action is passed as an instance `[MulSemiringAction (Multiplicative Fq) (Polynomial Fq)]` pinned by the hypothesis `hact : c • p = p.comp (X + C (Multiplicative.toAdd c))`, together with the (true for translations) instance `[SMulCommClass (Multiplicative Fq) Fq (Polynomial Fq)]` that Mathlib's `FixedPoints.subalgebra` needs; such an action exists (translations compose: $(p(X + b))(X + a) = p(X + a + b)$, and $p \mapsto p(X + c)$ is an $\mathbb{F}_q$-algebra map), so the hypotheses are satisfiable and the statement is not vacuous. The invariant ring is `FixedPoints.subalgebra Fq (Polynomial Fq) (Multiplicative Fq)`. Part 1 is an `AlgEquiv` `e` with `(e g : Polynomial Fq) = g.comp (X ^ Fintype.card Fq - X)`; part 2 is Mathlib's `IsGaloisGroup` (faithful, commuting with the base, invariants equal to the base); part 3 is `Module.Finite`; part 4 is `Q.inertia (Multiplicative Fq) = ⊥` for every prime `Q`. Example: for $q = 2$, the invariants of $p(X) \mapsto p(X + 1)$ in $\mathbb{F}_2[X]$ are the polynomials in $X^2 + X$, e.g. $X^4 + X = (X^2 + X)^2 + (X^2 + X)$.
-- source:
--   E. Artin and O. Schreier (1927); N. M. Katz, Sommes exponentielles, Asterisque 79 (1980), and P. Deligne, SGA 4 1/2, Sommes trig. (Artin-Schreier covering $x \mapsto x^q - x$ of the affine line and the sheaves $\mathcal{L}_\psi$); S. Lang, Algebra, Chapter VI, Section 6 (Artin-Schreier extensions)

import Mathlib

set_option autoImplicit false

theorem FiniteField.artinSchreier_translate_invariants_algEquiv_and_isGaloisGroup
    (Fq : Type) [Field Fq] [Fintype Fq]
    [MulSemiringAction (Multiplicative Fq) (Polynomial Fq)]
    [SMulCommClass (Multiplicative Fq) Fq (Polynomial Fq)]
    (hact : ∀ (c : Multiplicative Fq) (p : Polynomial Fq),
      c • p = p.comp (Polynomial.X + Polynomial.C (Multiplicative.toAdd c))) :
    (∃ e : Polynomial Fq ≃ₐ[Fq] FixedPoints.subalgebra Fq (Polynomial Fq) (Multiplicative Fq),
      ∀ g : Polynomial Fq,
        (e g : Polynomial Fq) = g.comp (Polynomial.X ^ Fintype.card Fq - Polynomial.X)) ∧
    IsGaloisGroup (Multiplicative Fq) (FixedPoints.subalgebra Fq (Polynomial Fq) (Multiplicative Fq))
      (Polynomial Fq) ∧
    Module.Finite (FixedPoints.subalgebra Fq (Polynomial Fq) (Multiplicative Fq)) (Polynomial Fq) ∧
    ∀ Q : Ideal (Polynomial Fq), Q.IsPrime → Q.inertia (Multiplicative Fq) = ⊥ := by
  sorry
