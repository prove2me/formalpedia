-- Prove2me | Theorems.Thm_DiazModulus_sixExponentials_cannot_refute_candidate
-- name    : DiazModulus.sixExponentials_cannot_refute_candidate
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T19:23:55.671713+00:00
-- url     : https://prove2.me/theorems/de25fa09-b094-4a91-a49a-1b0face79465
-- title:
--   No six-exponentials template fits a candidate's certificate span, but the four-exponentials one does
-- statement:
--   **A six exponentials template cannot be built out of a candidate's own certificate span — and
--   the four exponentials template still can.**
--
--   Let $u$ be a candidate: $u \neq 0$, $|u|$ algebraic, $e^{u}$ algebraic. Write $c = u\bar u = |u|^2$,
--   a non-zero algebraic number. Everything such an argument can certify about $u$ out of $u$ alone lies
--   in the $\bar{\mathbb{Q}}$-subspace $V = \operatorname{span}_{\bar{\mathbb{Q}}}\{1, u, \bar u\}$:
--   $1 \in \tilde{\mathcal L}$, $u \in \mathcal L$, $\bar u \in \mathcal L$ because
--   $e^{\bar u} = \overline{e^{u}}$, and $c \in \bar{\mathbb{Q}} = \bar{\mathbb{Q}}\cdot 1$.
--
--   Call a *$2\times n$ template* a pair of $\bar{\mathbb{Q}}$-linearly independent families
--   $x : \mathrm{Fin}\,2 \to \mathbb{C}$ and $y : \mathrm{Fin}\,n \to \mathbb{C}$ all of whose $2n$
--   products $x_i y_j$ are certified. The six exponentials theorems are $n = 3$; the four exponentials
--   theorems are $n = 2$.
--
--   The three clauses are:
--
--   1. $V \leq \tilde{\mathcal L}$ — the span really is a legitimate certificate space, so the
--      statement is about the hypotheses the exponentials theorems actually consume.
--   2. **Sharpness.** Under Hermite–Lindemann, $\dim_{\bar{\mathbb{Q}}} V = 3$ exactly, and the
--      $2\times 2$ template $x = (1,\bar u)$, $y = (1,u)$, with entries $1, u, \bar u, c$, does land in
--      $V$. That is precisely the template of the mission's proved
--      `diaz_of_strongFourExponentials_and_hermite_lindemann`.
--   3. **The no-go.** No $2\times 3$ template lands in $V$. This clause carries no hypothesis on $u$ at
--      all: it is a theorem about every complex number, and in particular it is not vacuous on the
--      (conjecturally empty) set of candidates.
--
--   **Mechanism.** Independence of $x$ gives $x_0 \neq 0$ and $s = x_1/x_0 \notin \bar{\mathbb{Q}}$.
--   Put $z_j = x_0 y_j$. If $y$ is independent so is $z$, so $\operatorname{span} z$ has dimension $n$;
--   when $\dim V \le n$ this forces $\operatorname{span} z = V$, and then $sV \subseteq V$ because
--   $s z_j = x_1 y_j \in V$. A non-zero finitely generated $\bar{\mathbb{Q}}$-submodule of
--   $\mathbb{C}$ stable under multiplication by $s$ makes $s$ integral over $\bar{\mathbb{Q}}$, hence
--   algebraic over $\mathbb{Q}$, hence in $\bar{\mathbb{Q}}$ — a contradiction. At $n = 2$ the step
--   $\operatorname{span} z = V$ fails, $2 < 3$, which is exactly why the strong four exponentials
--   template survives. The threshold is the dimension of the certificate space and nothing else.
--
--   **What it does not claim.** Forbidding $2\times 3$ templates with entries anywhere in
--   $\tilde{\mathcal L}$ is D. Roy's strong six exponentials *theorem* (J. Number Theory **41** (1992);
--   Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Corollary 11.16), which is proved
--   but has no formal proof in this environment. What is proved here is the $u$-generated fragment, a
--   statement about $\mathbb{C}$ with no transcendence input.
--
--   **Prior art.** Clause 3 is also an instance of a theorem of Roy on spaces of dimension at most
--   three (D. Roy, Acta Math. **175** (1995), Theorem 3.4; Waldschmidt, op. cit., Lemma 12.16 and
--   Exercise 12.10): a matrix with linearly independent rows and columns and entries in such a space has
--   rank at least $(d+\ell)/4$, so a $2\times 3$ one has rank $2$.
-- source:
--   New formal statement of the Diaz modulus mission, 7 September 2026 (C. Perassi). Clause 3 is an instance of D. Roy, Points whose coordinates are logarithms of algebraic numbers on algebraic varieties, Acta Math. 175 (1995), 49–73, Theorem 3.4 (M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Lemma 12.16 and Exercise 12.10).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem sixExponentials_cannot_refute_candidate (u : ℂ) :
    (IsCandidate u → Submodule.span Qbar ({1, u, conj u} : Set ℂ) ≤ LogAlgTilde) ∧
    (IsCandidate u → HermiteLindemann →
      Module.finrank Qbar (Submodule.span Qbar ({1, u, conj u} : Set ℂ)) = 3 ∧
      ∃ x y : Fin 2 → ℂ,
        LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) ∧
    (∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x →
      LinearIndependent (↥Qbar) y →
      ¬ ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) := by sorry
end DiazModulus
