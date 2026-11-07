-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_2_3
-- name    : AdaptiveSparsify.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:31.8692+00:00
-- url     : https://prove2.me/theorems/83611b29-9760-4e25-a20f-3a196ffffed6
-- title:
--   Lemma 2.3 (corrected: adds $A^\top A\preceq M$) — leverage overestimate sampling against a reference matrix $M$
-- statement:
--   Let $A$ be an $n\times d$ matrix with rows $a_i$, $n\ge2$, let $M$ be symmetric positive definite with $A^\top A\preceq M$, and let $w_i\ge a_i^\top M^{-1}a_i$. Put $p_i=w_i/\sum_iw_i$ and $T=\lceil100\epsilon^{-2}\log n\sum_iw_i\rceil$ for $\epsilon\in(0,1]$. Let $i_1,\dots,i_T$ be independent indices with $\Pr[i_j=i]=p_i$, and let $\tilde A$ have rows $(p_{i_j}T)^{-1/2}a_{i_j}$. Then, except with probability at most $n^{-10}$,
--
--   $$-\epsilon M\preceq A^\top A-\tilde A^\top\tilde A\preceq\epsilon M.$$
--
--   The checker's Gram matrices and the matrix $H$ of Algorithm 1 come from this sampling.
--
--   Differences from the source:
--   - correction: M any symmetric positive definite matrix → A⊤A ⪯ M is added; reason: as printed the lemma fails: d = 1, n = 1000, all a_i = 1, M = 0.1, w_i = 20 on half the rows and 10 on the others, ε = 1/2 gives Σw = 15000, T = 41,446,532, and A⊤A − Ã⊤Ã has standard deviation 0.0549 against εM = 0.05, so failure probability about 0.36 (normal approximation); both uses satisfy A⊤A ⪯ M
--   - reading: T := 100ε⁻² log n Σw_i → T = ⌈100ε⁻² log n Σw_i⌉; reason: the printed count need not be an integer
--   - reading: ε and n unrestricted → ε ∈ (0, 1], n ≥ 2, natural logarithm; reason: for large ε the printed T gives no polynomially small failure; at n = 1, log n = 0
--   - reading: "whp" → failure at most n^{−10}; reason: the constant 100 is fixed, so the exponent is fixed: Bernstein gives exponent at least 37.5 log n with dimension factor at most 2n
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma 2.3, p.11; uses at pp.35, 42

import Mathlib
import Definitions.Def_AdaptiveSparsify_Checker

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 2.3**, p.11 (corrected: C3).

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma 2.3, p.11.

"If A = [a_1⊤, a_2⊤, …, a_n⊤] is a n × d matrix, M is a d × d symmetric positive definite matrix, and w_i s
are values such that w_i ≥ a_i⊤M⁻¹a_i. Let p_i = w_i / ∑_{i=1}^n w_i and for j = 1, …, T := 100ε⁻² log n ·
∑_{i=1}^n w_i let i_1, …, i_T ∈ [n] be independent random indices with Pr[i_j = i] = p_i. Let Ã ∈ R^{T×d} be a
matrix whose j-th row is (p_{i_j}T)^{−1/2}a_{i_j}. Then whp: −ϵM ⪯ A⊤A − Ã⊤Ã ⪯ ϵM."

**Formalization Note.** Correction C3 adds `A⊤A ⪯ M`, which holds at both uses (pp.35, 42). `T` is rounded
up, `ϵ ∈ (0, 1]` and `n ≥ 2`. With the printed `100` fixed, "whp" is the explicit bound `n^{-10}`. If all `w_i`
vanish then `A = 0` and `T = 0`, and the claim holds with the empty sample. -/
theorem lemma_2_3 {n d : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin d) ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosDef) (w : Fin n → ℝ)
    (hw : ∀ i, leverage M (A i) ≤ w i) (hAM : LoewnerLE (Aᵀ * A) M)
    (ϵ : ℝ) (hϵ₀ : 0 < ϵ) (hϵ₁ : ϵ ≤ 1) :
    let p : Fin n → ℝ := fun i => w i / ∑ i', w i'
    let T : ℕ := ⌈100 * (ϵ⁻¹) ^ 2 * Real.log n * ∑ i, w i⌉₊
    probOf (sampleWeight (K' := T) p) (fun idx =>
      ¬ (LoewnerLE (-(ϵ • M)) (Aᵀ * A - (sampledMatrix A p idx)ᵀ * sampledMatrix A p idx) ∧
         LoewnerLE (Aᵀ * A - (sampledMatrix A p idx)ᵀ * sampledMatrix A p idx) (ϵ • M))) ≤
      (n : ℝ) ^ (-10 : ℝ) := by sorry

end AdaptiveSparsify
