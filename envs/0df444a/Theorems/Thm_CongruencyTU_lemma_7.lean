-- Prove2me | Theorems.Thm_CongruencyTU_lemma_7
-- name    : CongruencyTU.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:58.088057+00:00
-- url     : https://prove2.me/theorems/9f926aa7-d51c-4409-bb1b-dd850473bd32
-- title:
--   Lemma 7 (Decomposition lemma): $y-x_0$ splits in strongly polynomial time into elementary vectors that can be freely combined
-- statement:
--   Let $T\in\{-1,0,1\}^{k\times n}$ be totally unimodular, $b\in\mathbb Z^k$, and let $x_0,y\in\mathbb Z^n$ both satisfy $Tx\le b$. Then one can determine in strongly polynomial time vectors $y^1,\dots,y^n\in\mathbb Z^n$ and $\lambda_1,\dots,\lambda_n\in\mathbb Z_{\ge0}$ with
--   $$y-x_0=\sum_{i=1}^n\lambda_i y^i$$
--   such that
--
--   1. $y^1,\dots,y^n$ are elementary with respect to $T$;
--   2. for all $\mu_1,\dots,\mu_n\in\mathbb Z_{\ge0}$ with $\mu_i\le\lambda_i$, the vector $\tilde y:=x_0+\sum_i\mu_iy^i$ satisfies $T\tilde y\le b$.
--
--   The lemma is the basic tool for building new solutions of the relaxation from old ones, and drives the bounds on scalar products (Lemma 25).
--
--   **Formalization Note** One deterministic program reads $[k,n]$, $T$, $b$, $x_0$, $y$ and outputs $y^1,\dots,y^n$ followed by $\lambda_1,\dots,\lambda_n$.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - encoding: "determine y¹, …, yⁿ and λ₁, …, λₙ" → the output list y¹ ++ ⋯ ++ yⁿ ++ (λ₁, …, λₙ) of one deterministic program on [k, n] ++ T ++ b ++ x₀ ++ y; reason: a fixed format for the algorithm's answer
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.5 (PDF p.6), Lemma 7

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Appendable

open Matrix

namespace CongruencyTU

/-- **Lemma 7 (Decomposition lemma)** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.5, PDF p.6): "Let T ∈ {−1, 0, 1}^{k×n} be a totally
unimodular matrix, let b ∈ ℤ^k, and let x₀, y ∈ ℤⁿ be two solutions of the system Tx ≤ b. Then, we
can determine in strongly polynomial time y¹, …, yⁿ ∈ ℤⁿ and λ₁, …, λₙ ∈ ℤ_{≥0} such that
y − x₀ = Σᵢ λᵢ yⁱ with the following properties: (i) y¹, …, yⁿ are elementary with respect to T.
(ii) For µ₁, …, µₙ ∈ ℤ_{≥0} with µᵢ ≤ λᵢ for all i ∈ [n], the vector ỹ := x₀ + Σᵢ µᵢ yⁱ satisfies
Tỹ ≤ b."

One deterministic strongly polynomial program that, on `[k, n] ++ T ++ b ++ x₀ ++ y`, outputs
`y¹ ++ ⋯ ++ yⁿ ++ (λ₁, …, λₙ)` with these properties.

**Formalization Note.** `[n]` is `Fin n`; `T` totally unimodular (its entries are then in
`{−1, 0, 1}`). The machine is that of `Def_CongruencyTU_Machine`. -/
theorem lemma_7 :
    ∃ (P : Program) (p q : Polynomial ℕ), ∀ {k n : ℕ} (T : Matrix (Fin k) (Fin n) ℤ)
      (b : Fin k → ℤ) (x₀ y : Fin n → ℤ), T.IsTotallyUnimodular → T *ᵥ x₀ ≤ b → T *ᵥ y ≤ b →
      DetRunOK P ([(k : ℤ), (n : ℤ)] ++ encMat T ++ encVec b ++ encVec x₀ ++ encVec y) p q ∧
      ∃ (ys : Fin n → Fin n → ℤ) (lam : Fin n → ℕ),
        detOut P ([(k : ℤ), (n : ℤ)] ++ encMat T ++ encVec b ++ encVec x₀ ++ encVec y) p =
          (List.ofFn fun i => encVec (ys i)).flatten ++ List.ofFn (fun i => (lam i : ℤ)) ∧
        y - x₀ = ∑ i, (lam i : ℤ) • ys i ∧
        (∀ i, IsElementary T (ys i)) ∧
        ∀ μ : Fin n → ℕ, (∀ i, μ i ≤ lam i) → T *ᵥ (x₀ + ∑ i, (μ i : ℤ) • ys i) ≤ b := by sorry

end CongruencyTU
