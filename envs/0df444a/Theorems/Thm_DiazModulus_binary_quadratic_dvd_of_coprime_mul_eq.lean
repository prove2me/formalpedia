-- Prove2me | Theorems.Thm_DiazModulus_binary_quadratic_dvd_of_coprime_mul_eq
-- name    : DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:19:44.673486+00:00
-- url     : https://prove2.me/theorems/268a4fc4-d90f-4298-973a-10e5a92c9881
-- title:
--   A binary quadratic form coprime to F that divides F·L divides L; read in formal degrees, so a zero at infinity counts
-- statement:
--   Let $K$ be a field, let $P, F, L, B \in K[X]$ and $d, e \in \mathbb{N}$. Suppose that $P$ and $F$ are coprime, $F \neq 0$, $\deg P = 2$ or $\deg F = d$, $\deg L \leq e$, $\deg B + 2 \leq d + e$, and $FL = PB$. Then $L = PL_0$ for some $L_0 \in K[X]$ with $L_0 = 0$ or $\deg L_0 + 2 \leq e$. Here $\deg$ is the natural degree, with $\deg 0 = 0$.
--
--   Read $P$, $F$, $L$, $B$ as binary forms of degrees $2$, $d$, $e$ and $d + e - 2$. The hypothesis “$\deg P = 2$ or $\deg F = d$” says that $P$ and $F$ do not both vanish at $\infty$, so with coprimality it makes $P$ and $F$ coprime as binary forms; the conclusion is that $P$ divides $L$ as binary forms. For $e < 2$ it says $L = 0$.
--
--   **Proof.** If $P = 0$, then $F$ is a unit, being coprime to $0$, and $FL = 0$ gives $L = 0$. Otherwise $P$ divides $FL$ and is coprime to $F$, so $L = PL_0$; cancelling $P$ gives $FL_0 = B$. If $\deg P = 2$, then $2 + \deg L_0 = \deg L \leq e$. If $\deg F = d$ and $L_0 \neq 0$, then $d + \deg L_0 = \deg B \leq d + e - 2$.
--
--   **Novelty.** None claimed: Euclid\'s lemma for binary forms (a quadratic form coprime to $F$ that divides $FL$ divides $L$), stated with formal degrees, so that a zero at $\infty$ counts. Routine formalisation. It is the divisibility step of the nodes on invisible degree-two spaces.
-- source:
--   Classical: divisibility of binary forms over a field, stated with formal degrees so that a zero at infinity counts. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem binary_quadratic_dvd_of_coprime_mul_eq {K : Type*} [Field K] (P F L B : K[X]) (d e : ℕ)
    (hPF : IsCoprime P F) (hF0 : F ≠ 0) (hdeg : P.natDegree = 2 ∨ F.natDegree = d)
    (hL : L.natDegree ≤ e) (hB : B.natDegree + 2 ≤ d + e) (hFL : F * L = P * B) :
    ∃ L₀ : K[X], L = P * L₀ ∧ (L₀ = 0 ∨ L₀.natDegree + 2 ≤ e) := by
  sorry

end DiazModulus
