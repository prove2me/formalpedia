-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_razborov_distributional
-- name    : ExtensionComplexity.TSP.razborov_distributional
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:08:09.112829+00:00
-- url     : https://prove2.me/theorems/8b861caa-4ffe-4840-b85d-b747036c35fb
-- title:
--   Razborov's distributional bound for disjointness (displayed in the proof of Theorem 1)
-- statement:
--   For $n$-bit strings $a,b$ write $a^\top b$ for the number of common ones. There are constants $\alpha,\delta>0$, independent of $n$, such that for every sufficiently large $n$ there exist sets $A,B\subseteq\{0,1\}^n\times\{0,1\}^n$ and a probability distribution $\mu$ on $\{0,1\}^n\times\{0,1\}^n$ with
--
--   1. $a^\top b=0$ for all $(a,b)\in A$, and $a^\top b=1$ for all $(a,b)\in B$;
--   2. $\mu(A)=3/4$;
--   3. for every rectangle $R=R_1\times R_2$ with $R_1,R_2\subseteq\{0,1\}^n$,
--   $$\mu(R\cap B)\ \ge\ \alpha\cdot\mu(R\cap A)-2^{-\delta n}.$$
--
--   The paper quotes this result of Razborov (in the form of Kushilevitz and Nisan) without proof; it is the input to Theorem 1, since a $1$-monochromatic rectangle of the support of $M(n)$ avoids $B$ and therefore carries little $\mu$-mass of $A$. The paper notes that $\alpha=1/135$ and $\delta=0.017$ work for large $n$.
--
--   **Formalization Note** "Sufficiently large $n$" is $n\ge N$ for some $N$; $\alpha,\delta$ are chosen before $N$ and $n$. $\mu$ is a nonnegative function summing to $1$, $\mu(S)$ is the sum of $\mu$ over $S$, and $2^{-\delta n}$ is a real power.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, §2, p. 17:8, displayed result in the proof of Theorem 1 (Kushilevitz–Nisan 1997, Example 3.22 and §4.6; Razborov 1992)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_CorrelationMatrix

open Classical

namespace ExtensionComplexity.TSP

/-- Fiorini et al., J. ACM 62(2) (2015), Art. 17, §2, p. 17:8, the result displayed in the proof of
Theorem 1 (Kushilevitz–Nisan 1997, Example 3.22 and §4.6; Razborov 1992): there are constants
`α, δ > 0`, independent of `n`, such that for every sufficiently large `n` there are sets
`A, B ⊆ {0,1}^n × {0,1}^n` and a probability distribution `μ` on `{0,1}^n × {0,1}^n` with
`aᵀb = 0` on `A`, `aᵀb = 1` on `B`, `μ(A) = 3/4`, and for every rectangle `R = R₁ × R₂`,
`μ(R ∩ B) ≥ α · μ(R ∩ A) − 2^{−δn}`. -/
theorem razborov_distributional :
    ∃ α δ : ℝ, 0 < α ∧ 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∃ (A B : Finset ((Fin n → Bool) × (Fin n → Bool))) (μ : (Fin n → Bool) × (Fin n → Bool) → ℝ),
        (∀ p, 0 ≤ μ p) ∧ (∑ p, μ p) = 1 ∧
        (∀ p ∈ A, bitDot p.1 p.2 = 0) ∧ (∀ p ∈ B, bitDot p.1 p.2 = 1) ∧
        (∑ p ∈ A, μ p) = 3 / 4 ∧
        ∀ R₁ R₂ : Set (Fin n → Bool),
          α * (∑ p ∈ A.filter (fun p => p.1 ∈ R₁ ∧ p.2 ∈ R₂), μ p)
              - (2 : ℝ) ^ (-(δ * n)) ≤
            ∑ p ∈ B.filter (fun p => p.1 ∈ R₁ ∧ p.2 ∈ R₂), μ p := by sorry

end ExtensionComplexity.TSP
