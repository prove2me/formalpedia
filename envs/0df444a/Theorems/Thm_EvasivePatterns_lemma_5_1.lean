-- Prove2me | Theorems.Thm_EvasivePatterns_lemma_5_1
-- name    : EvasivePatterns.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:35.038952+00:00
-- url     : https://prove2.me/theorems/9c1d049c-8d8e-4c21-bca8-b57a7e7194d1
-- title:
--   Lemma 5.1 — primitive Wronskian: $\mathrm{cont}(W_Q)=1$ on the grid-and-tail shape
-- statement:
--   Let $p, k \ge 1$, $m = kp + r$ with $0 \le r < p$, and let $S = \{0, p, \dots, kp\} \cup E$ with $E \subseteq (\max\{p, m-p\}, m]$, $E \cap p\mathbb Z = \varnothing$, $\max S = m$ (the shape of Theorem 3.1). Assume $E \ne \varnothing$ and $\gcd S = 1$. Then for every polynomial
--   $$
--   Q(z) = \sum_{j \in S} a_j z^j, \qquad a_0 = 1, \quad a_j \in \{\pm 1\},
--   $$
--   the reciprocal Wronskian has content one: $\mathrm{cont}(W_Q) = 1$.
--
--   Primitivity of $W_Q$ is the arithmetic obstruction that later rules out root-of-unity rotations of the distinguished factor.
--
--   Differences from the source:
--   - encoding: Q(z) = Σ_{j∈S} a_j z^j with a_0 = 1, a_j ∈ {±1} → supp Q = S, Q.coeff 0 = 1, coefficients ±1 on S; reason: same polynomials
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Lemma 5.1, p.7 (PDF p.8), lines 222–223; shape of Theorem 3.1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_EvasivePatterns_recipWronskian

namespace EvasivePatterns

/-- **Lemma 5.1 (Primitive Wronskian).** Let `S` have the shape in Theorem 3.1, with `E ≠ ∅` and
`gcd S = 1`. For any polynomial `Q(z) = Σ_{j∈S} a_j z^j` with `a_0 = 1` and `a_j ∈ {±1}`, one has
`cont(W_Q) = 1`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Lemma 5.1, printed p. 7 (PDF p. 8), lines 222–223; the shape of Theorem 3.1,
printed p. 4 (PDF p. 5), lines 133–134.

**Formalization Note** The shape of Theorem 3.1: `p, k ≥ 1`, `m = kp + r`, `0 ≤ r < p`,
`S = {0, p, …, kp} ∪ E`, `E ⊆ (max{p, m − p}, m]`, `E ∩ pℤ = ∅`, `max S = m`; all points are
natural numbers, so `S` is a `Finset ℕ`. `Q = Σ_{j∈S} a_j z^j` with `a_j ∈ {±1}` means
`supp Q = S` with coefficients `±1` on `S`, and `a_0 = 1`. `cont` is `Polynomial.content`. -/
theorem lemma_5_1 (p k r m : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) (hr : r < p) (hm : m = k * p + r)
    (E : Finset ℕ) (hE : ∀ e ∈ E, max p (m - p) < e ∧ e ≤ m) (hEp : ∀ e ∈ E, ¬ p ∣ e)
    (S : Finset ℕ) (hS : S = (Finset.range (k + 1)).image (fun j => j * p) ∪ E)
    (hmax : S.max = (m : WithBot ℕ)) (hEne : E.Nonempty) (hgcd : S.gcd id = 1)
    (Q : Polynomial ℤ) (hQS : Q.support = S) (hQ0 : Q.coeff 0 = 1)
    (hQpm : ∀ j ∈ S, Q.coeff j = 1 ∨ Q.coeff j = -1) :
    (recipWronskian Q).content = 1 := by sorry

end EvasivePatterns
