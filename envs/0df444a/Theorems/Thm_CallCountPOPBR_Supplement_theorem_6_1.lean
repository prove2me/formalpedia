-- Prove2me | Theorems.Thm_CallCountPOPBR_Supplement_theorem_6_1
-- name    : CallCountPOPBR.Supplement.theorem_6_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-17T00:06:57.436038+00:00
-- url     : https://prove2.me/theorems/68f3109b-ac40-48a9-9d8f-58d73a09d4b9
-- title:
--   Theorem 6.1 — periodic branching implies rationality
-- statement:
--   Let $C:\mathbb N\to\mathbb N$, let $d,p\ge1$, and let $a_j(n)\in\mathbb N$. Suppose that beyond some threshold $N_0\ge d$,
--
--   $$
--   C_n=1+\sum_{j=1}^{d}a_j(n)C_{n-j},
--   $$
--
--   and $a_j(n+p)=a_j(n)$ for every $1\le j\le d$. Then there are rational coefficients $q_0,\ldots,q_{d+1}$ with $q_{d+1}=1$ and a threshold $N_1$ such that
--
--   $$
--   \sum_{k=0}^{d+1}q_kC_{n+kp}=0\qquad(n\ge N_1).
--   $$
--
--   In addition, the ordinary generating function is rational: there are $P,Q\in\mathbb Q[X]$ with $Q(0)=1$ and
--
--   $$
--   \left(\sum_{n\ge0}C_nz^n\right)Q(z)=P(z)
--   $$
--
--   as formal power series.
--
--   Differences from the source:
--   - reading: a homogeneous recurrence involving $C_n,\ldots,C_{n+(d+1)p}$ → rational coefficients with the coefficient of $C_{n+(d+1)p}$ equal to one; reason: the paper's proof explicitly takes the monic characteristic polynomial of the period product
--   - encoding: the recurrence and coefficient periodicity hold for all sufficiently large $n$ → one explicit common threshold $N_0\ge d$ is supplied and both properties hold for every $n\ge N_0$; reason: taking the maximum of the two eventual thresholds and $d$ gives exactly this form and makes every subtraction $n-j$ genuine
--   - encoding: rational ordinary generating function → polynomials $P,Q\in\mathbb Q[X]$ with $Q(0)=1$ and $C(z)Q(z)=P(z)$ in formal power series; reason: this is the standard denominator-cleared definition and excludes a zero denominator
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Eq. (13) and Theorem 6.1, pp.10–11

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **Theorem 6.1 (Periodic branching implies rationality).** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), §6 and Theorem 6.1, p.10:
"Fix a maximum offset d ≥ 1. For all sufficiently large n, let C_n = 1 + ∑_{j=1}^{d} a_j(n) C_{n−j},
a_j(n) ∈ ℤ_{≥0}. (13) Assume there is a period p ≥ 1 such that a_j(n + p) = a_j(n) for every j and
all sufficiently large n. … Under (13), the sequence (C_n) eventually satisfies a homogeneous
constant-coefficient recurrence involving the terms C_n, C_{n+p}, . . . , C_{n+(d+1)p}. Consequently
its ordinary generating function ∑_{n≥0} C_n z^n is rational."

Hypotheses: (13) and the periodicity of `a_j` (`1 ≤ j ≤ d`) hold for all `n ≥ N₀`; `C_0, …` below
`N₀` are arbitrary. Conclusions:
1. there are rationals `q_0, …, q_{d+1}` with `q_{d+1} = 1` and a threshold `N₁` with
   `∑_{k=0}^{d+1} q_k C_{n+kp} = 0` for all `n ≥ N₁`;
2. `∑ C_n z^n = P(z)/Q(z)` in `ℚ⟦z⟧` for polynomials `P, Q` with `Q(0) = 1`.

**Formalization Note.** The recurrence is monic in `C_{n+(d+1)p}` (the proof's characteristic
polynomial), which excludes the trivial all-zero recurrence. The threshold satisfies `d ≤ N₀`, so
`n - j` is the true difference throughout (13). Rationality is `C(z) · Q(z) = P(z)` with
`Q(0) = 1`, so `Q` is invertible in `ℚ⟦z⟧`. -/
theorem theorem_6_1 (C : ℕ → ℕ) (d p : ℕ) (hd : 1 ≤ d) (hp : 1 ≤ p) (a : ℕ → ℕ → ℕ) (N₀ : ℕ)
    (hN₀ : d ≤ N₀)
    (hrec : ∀ n, N₀ ≤ n → C n = 1 + ∑ j ∈ Finset.Icc 1 d, a j n * C (n - j))
    (hper : ∀ n, N₀ ≤ n → ∀ j ∈ Finset.Icc 1 d, a j (n + p) = a j n) :
    (∃ (q : ℕ → ℚ) (N₁ : ℕ), q (d + 1) = 1 ∧
      ∀ n, N₁ ≤ n → ∑ k ∈ Finset.range (d + 2), q k * (C (n + k * p) : ℚ) = 0) ∧
    (∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧
      PowerSeries.mk (fun n => (C n : ℚ)) * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ)) := by sorry

end CallCountPOPBR.Supplement
