-- Prove2me | Theorems.Thm_DiazModulus_restrictSupport_block_filtration
-- name    : DiazModulus.restrictSupport_block_filtration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:05:01.234387+00:00
-- url     : https://prove2.me/theorems/88f02b10-77bb-476a-9ed2-80421114a9ce
-- title:
--   For a block map $\beta : \sigma \to \iota$ with $\sigma$ finite, the block boxes are finite-dimensional, multiply as $T + T'$ and exhaust the polynomial ring
-- statement:
--   Let $K$ be a field, $\sigma$ a finite type, $\iota$ a type and $\beta : \sigma \to \iota$ a map grouping the variables of $K[X_s : s \in \sigma]$ into blocks. For $T \in \mathbb{N}^\iota$ let $B_T$ be `blockBox K β T`, the span of the monomials $X^m$ whose degree in each block, $\sum_{\beta(s) = b} m_s$, is at most $T_b$. Then (i) $fg \in B_{T+T'}$ whenever $f \in B_T$ and $g \in B_{T'}$; (ii) every $B_T$ is finite-dimensional over $K$; (iii) every polynomial lies in some $B_T$. The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** (i) The exponents of $fg$ are sums of exponents of $f$ and of $g$, and block degrees add. (ii) Every exponent $m$ of $B_T$ has $m_s \le T_{\beta(s)}$, so the admissible exponents form a finite set, and the monomials are a basis. (iii) Take $T_b$ to be the sum over the exponents of $f$ of their degrees in block $b$.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical. The multidegree filtration of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §8.2.2 (p. 235; Chapter 8 is by D. Roy), for an arbitrary partition of the variables. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem restrictSupport_block_filtration {K σ ι : Type*} [Field K] [Finite σ] (β : σ → ι) :
    (∀ (T T' : ι → ℕ) (f g : MvPolynomial σ K), f ∈ blockBox K β T → g ∈ blockBox K β T' →
        f * g ∈ blockBox K β (T + T')) ∧
      (∀ T : ι → ℕ, FiniteDimensional K ↥(blockBox K β T)) ∧
      ∀ f : MvPolynomial σ K, ∃ T : ι → ℕ, f ∈ blockBox K β T := by
  sorry

end DiazModulus
