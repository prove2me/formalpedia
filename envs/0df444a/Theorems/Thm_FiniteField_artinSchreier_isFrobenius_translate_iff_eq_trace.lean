-- Prove2me | Theorems.Thm_FiniteField_artinSchreier_isFrobenius_translate_iff_eq_trace
-- name    : FiniteField.artinSchreier_isFrobenius_translate_iff_eq_trace
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T05:39:18.778942+00:00
-- url     : https://prove2.me/theorems/d276bfa7-d153-4b63-b8a8-c456b8b17e81
-- title:
--   Frobenius of the Artin–Schreier cover $x \mapsto x^q - x$ of the affine line: at a point $t$ it is the translation $x \mapsto x + \mathrm{Tr}_{k(t)/\mathbb{F}_q}(t)$
-- statement:
--   Let $\mathbb{F}_q$ be a finite field with $q$ elements. Make $\mathbb{F}_q[x]$ an algebra over $\mathbb{F}_q[T]$ through the Artin–Schreier map $T \mapsto x^q - x$ (the Artin–Schreier cover $\mathbb{A}^1 \to \mathbb{A}^1$, whose deck group $\mathbb{F}_q$ acts by the translations $x \mapsto x + c$). Let $P$ be a maximal ideal of $\mathbb{F}_q[T]$, with residue field $k(P) = \mathbb{F}_q[T]/P$ of cardinality $N(P)$, and let $Q$ be an ideal of $\mathbb{F}_q[x]$ lying over $P$:
--
--   $$\{\, g \in \mathbb{F}_q[T] \;:\; g(x^q - x) \in Q \,\} = P.$$
--
--   Then for $c \in \mathbb{F}_q$ the translation $\sigma_c : f(x) \mapsto f(x + c)$ is an arithmetic Frobenius at $Q$, i.e.
--
--   $$f(x + c) \equiv f(x)^{N(P)} \pmod{Q} \qquad \text{for all } f \in \mathbb{F}_q[x],$$
--
--   if and only if
--
--   $$c = \mathrm{Tr}_{k(P)/\mathbb{F}_q}\bigl(T \bmod P\bigr).$$
--
--   So at every point above $P$ the Frobenius of the Artin–Schreier cover is the translation by the trace of $T$ from the residue field $k(P)$ down to $\mathbb{F}_q$, and no other translation has this property.
--
--   Role: this is the computation that identifies the Frobenius traces of the Artin–Schreier sheaves $\mathcal{L}_\psi$ (the sheaves obtained from this $\mathbb{F}_q$-torsor and an additive character $\psi$ of $\mathbb{F}_q$) with $\psi(\mathrm{Tr}_{k(t)/\mathbb{F}_q}(t))$, up to the sign convention for $\psi$; it is the starting point for writing additive character sums over finite fields as traces of Frobenius (Deligne, SGA 4½, *Sommes trigonométriques*).
--
--   **Formalization Note**: both $\mathbb{F}_q[T]$ and $\mathbb{F}_q[x]$ are `Polynomial Fq`; the structure map is `Polynomial.aeval (X ^ Fintype.card Fq - X)`, and "$Q$ lies over $P$" is `Q.comap (Polynomial.aeval (X ^ Fintype.card Fq - X)) = P`. The translation $\sigma_c$ is `f.comp (X + C c)`, $N(P)$ is `Nat.card (Polynomial Fq ⧸ P)`, and $\mathrm{Tr}_{k(P)/\mathbb{F}_q}(T \bmod P)$ is `Algebra.trace Fq (Polynomial Fq ⧸ P)` applied to the class of `X` (the variable $T$ of the base) in the quotient. The left side of the equivalence is Mathlib's `IsArithFrobAt` condition for $\sigma_c$, written out. $Q$ is any ideal lying over $P$; the usual Frobenius element is the case of a prime $Q$.
-- source:
--   P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Mathematics 569, Springer 1977, "Sommes trigonométriques", Section 1 (the Lang torsor $x \mapsto x^q - x$ of the additive group and the trace of Frobenius)

import Mathlib

set_option autoImplicit false

theorem FiniteField.artinSchreier_isFrobenius_translate_iff_eq_trace
    (Fq : Type*) [Field Fq] [Fintype Fq]
    (P : Ideal (Polynomial Fq)) [P.IsMaximal] (Q : Ideal (Polynomial Fq))
    (hQ : Q.comap (Polynomial.aeval (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq)) = P)
    (c : Fq) :
    (∀ f : Polynomial Fq,
        f.comp (Polynomial.X + Polynomial.C c) - f ^ Nat.card (Polynomial Fq ⧸ P) ∈ Q) ↔
      c = Algebra.trace Fq (Polynomial Fq ⧸ P) (Ideal.Quotient.mk P Polynomial.X) := by sorry
