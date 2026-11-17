-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_26
-- name    : DeepQOperator.Supplement.theorem_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:49:11.243201+00:00
-- url     : https://prove2.me/theorems/1f9a9511-7219-4bde-8f40-0830998baa67
-- title:
--   Theorem 26, p.71 — signed shared-design benchmark for independent Lipschitz rows
-- statement:
--   Let rows $i=1,\dots,m$ carry nonempty compact metric domains $\mathcal A_i$, bounds $B_i\ge0$ and Lipschitz constants $L_i\ge0$. Inputs are tuples $(f_i)$ of independent $L_i$-Lipschitz functions $f_i:\mathcal A_i\to[-B_i,B_i]$, $M_i=\max f_i$. A known $b\in\mathbb{R}^K$, $0<\gamma<1$ and a signed $A\in\mathbb{R}^{K\times m}$ fix the target $b+\gamma AM$. With $D_i$ as in (118), the deterministic adaptive minimax $\infty$-norm recovery error from at most $N$ exact scalar queries is
--   $$
--   \mathfrak R_N(A)=\frac\gamma2\min_{\substack{n_i\in\mathbb N_0\\ \sum_in_i\le N}}\ \max_{k\le K}\ \sum_i|A_{ki}|\,D_i(n_i). \tag{119}
--   $$
--   Fixed near-optimal covers with midpoint estimates attain the infimum in the limiting sense: for every $\eta>0$ there are an allocation with $\sum_in_i\le N$ and fixed sites whose midpoint estimate has worst error at most $\mathfrak R_N(A)+\eta$. The equality includes zero-query rows, constant rows ($L_i=0$) and unattained optimal covers.
--
--   The benchmark shows that, for independent rows, adaptive acquisition gives no advantage over a fixed allocation.
--
--   Differences from the source:
--   - encoding: the minimax error $\mathfrak R_N(A)$ → an infimum over deterministic adaptive algorithms (run with fuel $N$) of the supremum over the input class of the sup-norm error, in $\mathbb{R}_{\ge0}\cup\{\infty\}$; reason: Lean convention; neither needs to be attained
--   - encoding: infimal fill distance of $n$ sites → infimum over maps from $n$ indices to $\mathcal A_i$ (repetition allowed); reason: a set of at most $n$ distinct sites; the infimum is the same
--   - reading: attain the infimum in the limiting sense → for every $\eta>0$, an allocation and fixed sites whose midpoint estimate has worst error at most $\frac\gamma2(\text{allocation value})+\eta$; reason: the limiting sense of App. W.2
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 26 and eqs. (118)–(119), p.71 (PDF p.74); proof in Appendix W, pp.73–74 (PDF pp.76–77)

import Mathlib
import Definitions.Def_DeepQOperator_Supplement_LipschitzRows

open Finset

namespace DeepQOperator.Supplement

/-- **Theorem 26 (Signed shared-design benchmark)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive
Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256 9f8f3285…),
Theorem 26, p.71, PDF p.74; setting (118) p.71; proof Appendix W, pp.73–74).

Let rows `i = 1, …, m` carry nonempty compact metric domains `𝒜_i`, bounds `B_i ≥ 0` and Lipschitz
constants `L_i ≥ 0`, and let the inputs `(f_i)` range independently over `L_i`-Lipschitz functions
`f_i : 𝒜_i → [-B_i, B_i]`, with `M_i = max f_i`. For known `b ∈ ℝ^K`, `0 < γ < 1` and signed
`A ∈ ℝ^{K×m}`, the deterministic adaptive minimax infinity-norm recovery error of `b + γAM` from at most
`N` exact scalar queries is
`ℜ_N(A) = (γ/2) min_{n ∈ ℕ₀^m, Σ_i n_i ≤ N} max_{k ≤ K} Σ_i |A_ki| D_i(n_i)` (119),
with `D_i` from (118). Fixed near-optimal covers and midpoint estimates attain the infimum in the
limiting sense. The equality includes zero-query rows, constant rows (`L_i = 0`), and unattained optimal
covers.

**Formalization Note.** `minimaxError` is the infimum over deterministic adaptive algorithms
(`LipAlg`, run with fuel `N`) of the supremum over the product input class of the sup-norm error, in
`ℝ≥0∞`. `allocationValue` is the minimum over the finite set of allocations with `Σ n_i ≤ N`. The
limiting-attainment clause: for every `η > 0` there are an allocation with `Σ n_i ≤ N` and fixed sites
`x_i : Fin n_i → 𝒜_i` whose midpoint estimate (Appendix W.2) has worst error at most `ℜ_N(A) + η` over
the input class. The midpoint estimate reads `f` only at the chosen sites. -/
theorem theorem_26 :
    ∀ (m K : ℕ) (𝒜 : Fin m → Type) [∀ i, MetricSpace (𝒜 i)] [∀ i, CompactSpace (𝒜 i)]
      [∀ i, Nonempty (𝒜 i)] (Bd : Fin m → ℝ) (L : Fin m → NNReal) (b : Fin K → ℝ) (γ : ℝ)
      (Amat : Matrix (Fin K) (Fin m) ℝ) (N : ℕ),
      (∀ i, 0 ≤ Bd i) → 0 < γ → γ < 1 →
      minimaxError 𝒜 Bd L b γ Amat N = ENNReal.ofReal (γ / 2 * allocationValue 𝒜 Bd L Amat N) ∧
      ∀ η : ℝ, 0 < η →
        ∃ (n : Fin m → ℕ) (_ : ∑ i, n i ≤ N) (x : ∀ i, Fin (n i) → 𝒜 i),
          (⨆ (f : ∀ i, 𝒜 i → ℝ) (_ : InLipClass Bd L f),
            ENNReal.ofReal ‖midpointEstimate Bd L b γ Amat n x f - recTarget b γ Amat f‖) ≤
            ENNReal.ofReal (γ / 2 * allocationValue 𝒜 Bd L Amat N + η) := by sorry

end DeepQOperator.Supplement
