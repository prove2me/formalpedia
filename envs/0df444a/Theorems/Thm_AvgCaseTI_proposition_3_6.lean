-- Prove2me | Theorems.Thm_AvgCaseTI_proposition_3_6
-- name    : AvgCaseTI.proposition_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:40.132693+00:00
-- url     : https://prove2.me/theorems/0fbcc54a-c5b6-4971-9d9f-8f1ddc0d3ca8
-- title:
--   Proposition 3.6 — the normalized hull generator and the contraction generate $\mathrm M(n,q)$ and $\mathrm{Tr}(X)\ne0$ with probability $\ge1/3$
-- statement:
--   Sample $A_1,\dots,A_n$ independently and uniformly from $\mathrm M(n,q)$ and condition on the event $E$: the $A_i$ are linearly independent, $\dim H(\mathcal A)=1$ for $\mathcal A=\mathrm{span}\{A_i\}$, and the hull generator has exactly one $\mathbb F_q$-eigenvalue, nonzero and of algebraic multiplicity 1. Let $A$ be the hull generator normalized to eigenvalue $1$, $v=v(A)$ a nonzero left eigenvector of $A$ chosen by a fixed rule depending only on $A$, and
--   $$
--   X=\sum_{i=1}^{n}v_iA_i .
--   $$
--   There are an absolute constant $K$ and an absolute constant $c>0$ such that for every finite field $\mathbb F_q$, for all sufficiently large $n$ (depending on $q$), and for every such rule:
--   1. $\displaystyle \Pr[A,X\text{ do not generate }\mathrm M(n,q)\mid E]\le\frac{q-1}{q^n-1}+Kq^2\varepsilon_{\mathrm{gen}}(n,q)$;
--   2. $\displaystyle \frac{q-1}{q^n-1}+Kq^2\varepsilon_{\mathrm{gen}}(n,q)\le q^{-cn}$, i.e. the bound in 1 is $q^{-\Omega(n)}$;
--   3. $\Pr[\mathrm{Tr}(X)\ne0\mid E]\ge(1-q^{-1})(1-16q^{1-n})$;
--   4. $\Pr[A,X\text{ generate }\mathrm M(n,q)\text{ and }\mathrm{Tr}(X)\ne0\mid E]\ge1/3$.
--
--   Here $\varepsilon_{\mathrm{gen}}(n,q)$ is the generation-failure probability of Theorem 2.3. This is the final step of the average-case analysis of Theorem 1.1: on these first tensors the trace-normalized contraction gives a second canonical matrix, and the pair has scalar centralizer.
--
--   **Formalization Note** A "rule" is any map $v$ from matrices to row vectors such that $v(H)$ is a nonzero left eigenvector for the eigenvalue $1$ whenever $H$ has exactly one eigenvalue in $\mathbb F_q$, equal to $1$ and simple; the bounds hold for every such rule. Conditional probabilities are ratios of counts over the tuples in $E$. "Generate" is the unital subalgebra.
--
--   Differences from the source:
--
--   - reading: "choose a nonzero left eigenvector v = v(A) by a fixed rule depending only on A" → every map v giving a nonzero left eigenvector for eigenvalue 1 on matrices with a unique simple eigenvalue 1; the threshold N chosen before v; reason: the rule is arbitrary but fixed; the paper's threshold depends only on q
--   - reading: K an absolute constant; "= q^{−Ω(n)}" → ∃ K₀ and c > 0 before the field; the bound ≤ q^{−cn}; reason: Ω with an absolute constant, as for Theorem 2.3
--   - encoding: conditional probabilities given the event → ratios of counts over the tuples in the event; reason: uniform distribution on a finite set
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.6, Eqs. (8)–(9), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_AvgCaseTI_epsGen
import Definitions.Def_AvgCaseTI_normGen

set_option autoImplicit false

universe u

namespace AvgCaseTI

/-- **Proposition 3.6 (the normalized hull generator and the contraction generate `M(n, q)`, and the
contraction has nonzero trace, with constant probability).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.6, p.20
(PDF p.22). Sample `A₁, …, A_n` independently and uniformly from `M(n, q)` and condition on the event
`E`: they are linearly independent, `dim H(𝒜) = 1`, and the hull generator has exactly one
`F_q`-eigenvalue, nonzero and simple. Let `A` be the generator normalized to eigenvalue 1, `v = v(A)`
a nonzero left eigenvector chosen by a fixed rule, and `X = Σ_i v_i A_i`. There are an absolute
constant `K` and an absolute `c > 0` such that for every finite field and all sufficiently large `n`
(depending on `q`), for every such rule:
1. `Pr[A, X do not generate M(n, q) | E] ≤ (q − 1)/(qⁿ − 1) + K q² ε_gen(n, q)` (Eq. (8));
2. `(q − 1)/(qⁿ − 1) + K q² ε_gen(n, q) ≤ q^{−cn}` (the `= q^{−Ω(n)}` of Eq. (8));
3. `Pr[Tr(X) ≠ 0 | E] ≥ (1 − q^{−1})(1 − 16 q^{1−n})` (Eq. (9));
4. `Pr[A, X generate M(n, q) and Tr(X) ≠ 0 | E] ≥ 1/3`.

**Formalization Note.** The rule is any map `v` from matrices to row vectors such that `v(H)` is a
nonzero left eigenvector for the eigenvalue `1` whenever `H` has exactly one eigenvalue in `F_q`,
equal to `1` and simple; the bounds hold for every such rule. Conditional probabilities are ratios
of counts over `E`. `K` (named `K₀`) and `c` are chosen before the field; the threshold `N` depends
on the field. "Generate" is the unital subalgebra. -/
theorem proposition_3_6 :
    ∃ K₀ c : ℝ, 0 < c ∧ ∀ (F : Type u) [Field F] [Fintype F], ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ v : Mat F n → (Fin n → F),
        (∀ H : Mat F n, UniqueSimpleEig H → H.charpoly.IsRoot 1 →
          v H ≠ 0 ∧ Matrix.vecMul (v H) H = v H) →
        (Nat.card {A : Fin n → Mat F n // Prop36Event A ∧
            Algebra.adjoin F {normGen A, contraction (v (normGen A)) A} ≠ ⊤} : ℝ) /
            Nat.card {A : Fin n → Mat F n // Prop36Event A} ≤
          ((Fintype.card F : ℝ) - 1) / ((Fintype.card F : ℝ) ^ n - 1) +
            K₀ * (Fintype.card F : ℝ) ^ 2 * epsGen F n ∧
        ((Fintype.card F : ℝ) - 1) / ((Fintype.card F : ℝ) ^ n - 1) +
            K₀ * (Fintype.card F : ℝ) ^ 2 * epsGen F n ≤
          (Fintype.card F : ℝ) ^ (-(c * n)) ∧
        (1 - (Fintype.card F : ℝ)⁻¹) * (1 - 16 * (Fintype.card F : ℝ) ^ (1 - (n : ℝ))) ≤
          (Nat.card {A : Fin n → Mat F n // Prop36Event A ∧
              Matrix.trace (contraction (v (normGen A)) A) ≠ 0} : ℝ) /
            Nat.card {A : Fin n → Mat F n // Prop36Event A} ∧
        1 / 3 ≤
          (Nat.card {A : Fin n → Mat F n // Prop36Event A ∧
              Algebra.adjoin F {normGen A, contraction (v (normGen A)) A} = ⊤ ∧
              Matrix.trace (contraction (v (normGen A)) A) ≠ 0} : ℝ) /
            Nat.card {A : Fin n → Mat F n // Prop36Event A} := by sorry

end AvgCaseTI
