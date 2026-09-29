-- Prove2me | Theorems.Thm_Diaz_q_translate_unique
-- name    : Diaz.q_translate_unique
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:05:23.432732+00:00
-- url     : https://prove2.me/theorems/cd260bbc-5226-4730-aa6d-70922b91eea5
-- title:
--   Rational-translate rigidity: at most one non-zero rational translate stays on the locus
-- statement:
--   **Source.** This is Carlo Perassi's mathematics, the counting half of his rational-translate rigidity, unpublished apart from this node. Published on his mission with his permission. No novelty is claimed for it here; the argument is elementary.
--
--   **Statement.** Let $K \subset \mathbb{C}$ be a subfield with $\pi^2 \notin K$, and let $u$ satisfy $u\bar u \in K$. Put $T(u) = \{r \in \mathbb{Q} : (u + 2\pi i r)\overline{(u + 2\pi i r)} \in K\}$. Then $T(u)$ contains at most one non-zero element — so, with $0 \in T(u)$ always, $\#T(u) \leq 2$.
--
--   **Why $K$ and not $\overline{\mathbb{Q}}$.** The intended instance is $K = \overline{\mathbb{Q}}$, where $\pi^2 \notin K$ is Lindemann's theorem, and the hypothesis $u\bar u \in K$ is the defining condition of a Diaz candidate. Stating it over a general subfield keeps the node self-contained and free of any transcendence input: everything above the field axioms is the single hypothesis $\pi^2 \notin K$.
--
--   **What it strengthens.** The corresponding statement for *integer* translates is the exponential-fibre count, Theorem 3.3 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). This upgrades it to rational translates, and it is the step his original argument uses to isolate the obstruction in the single logarithm $i\pi$: outside the torsion branch, a second candidate in $T(u)$ forces $(i\pi)\nu \in \overline{\mathbb{Q}}^\times$ for some non-zero logarithm $\nu$, which is the configuration feeding the $e^{\pi^2}$ consequence (see `Diaz.indep_of_algebraic_product`).
--
--   **Proof.** For $r \in \mathbb{Q}$,
--   $$(u + 2\pi i r)\overline{(u + 2\pi i r)} = u\bar u + r\bigl(Z + 4\pi^2 r\bigr),\qquad Z := 2\pi i(\bar u - u),$$
--   a one-line expansion using $\overline{2\pi i r} = -2\pi i r$ and $i^2 = -1$. Subtracting $u\bar u \in K$ and dividing by the non-zero rational $r$ (rationals lie in every subfield) gives $Z + 4\pi^2 r \in K$, and likewise $Z + 4\pi^2 r' \in K$. Their difference is $4\pi^2(r - r') \in K$; if $r \neq r'$, dividing by the non-zero rational $4(r-r')$ puts $\pi^2$ in $K$, contrary to hypothesis.

import Mathlib

open ComplexConjugate

theorem Diaz.q_translate_unique {K : Subfield ℂ} {u : ℂ}
    (hρ : u * conj u ∈ K) (hπ : ((Real.pi : ℂ)) ^ 2 ∉ K)
    {r r' : ℚ} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (h : (u + 2 * (Real.pi : ℂ) * (r : ℂ) * Complex.I)
          * conj (u + 2 * (Real.pi : ℂ) * (r : ℂ) * Complex.I) ∈ K)
    (h' : (u + 2 * (Real.pi : ℂ) * (r' : ℂ) * Complex.I)
          * conj (u + 2 * (Real.pi : ℂ) * (r' : ℂ) * Complex.I) ∈ K) :
    r = r' := by sorry
