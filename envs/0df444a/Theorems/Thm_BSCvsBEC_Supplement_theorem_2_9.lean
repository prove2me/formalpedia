-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_2_9
-- name    : BSCvsBEC.Supplement.theorem_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:36:58.211677+00:00
-- url     : https://prove2.me/theorems/d852b336-daef-4360-94cb-d07dbcb795f1
-- title:
--   Theorem 2.9 — entropic Samorodnitsky inequalities $H_\alpha(Y)\ge(\log q)(1-\lambda)n+\mathbb E_{S\sim\lambda}H_\alpha(X_S)$
-- statement:
--   Let $|\Omega|=q$, $\rho\in[0,1]$ and $p=\frac{q-1}q(1-\rho)$. Let $X\in\Omega^n$ be a random variable and $Y$ the output of sending $X$ over $\mathrm{qSC}_p$. Then
--   $$H_\alpha(Y)\ \ge\ (\log q)(1-\lambda)n+\mathbb E_{S\sim\lambda}H_\alpha(X_S)$$
--   whenever $\lambda^*(\alpha,q,\rho)\le\lambda\le1$, in each of the three cases of Theorem 2.7:
--
--   1. any $q\ge2$ and $2\le\alpha\le\infty$, with $\lambda^*(\alpha,q,\rho)=1-H_\alpha(\mathrm{qSC}_p)/\log q$;
--   2. $q=2$ and $1<\alpha<2$, with $\lambda^*(\alpha,2,\rho)$ the optimal one-coordinate constant;
--   3. $q=2$ and $\alpha=1$ (Shannon entropy), with $\lambda^*(1,2,\rho)=\rho^2$.
--
--   Here $S\subseteq[n]$ contains each coordinate independently with probability $\lambda$, $X_S$ is the restriction of $X$ to $S$, and entropies are in bits. This is the entropic form of the Samorodnitsky inequalities; via qSC/qPSC duality it gives the linear-code case of the PSC–BEC comparisons.
--
--   **Formalization Note** The three cases are three conjuncts. Classical Rényi entropies are the published quantum Rényi entropy of the diagonal matrix of the pmf.
--
--   Differences from the source:
--   - reading: in the setting of Theorem 2.7 (ρ the parameter of T_ρ) → 0 ≤ ρ ≤ 1; reason: T_ρ and the convention (15) are set up for ρ ∈ [0, 1] (p.6)
--   - encoding: |Ω| = q → 2 ≤ Fintype.card Ω in case 1; reason: qSC_p (p/(q − 1)) and λ* (division by log q) are undefined for q = 1
--   - encoding: provided λ ≥ λ*(α, q, ρ) → λ* ≤ λ ≤ 1; reason: S ∼ λ is defined only for λ ∈ [0, 1]
--   - encoding: λ*(α, 2, ρ) for 1 < α < 2, the optimal n = 1 constant → lamStarB α ρ, the infimum of the λ ∈ [0, 1] for which the n = 1 case of (51) holds for every g ≥ 0; reason: this is the definition of the optimal constant
--   - encoding: H_α of a classical random variable → renyi α of the diagonal matrix of its pmf (renyiP); reason: the spectrum of diag(P) is the multiset of values of P; same values
--   - encoding: a random variable X on a finite set → its pmf P with IsPMF P; reason: Lean convention; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 2.9, eq. (53), p.11; Theorem 2.7, eq. (51), p.10

import Mathlib
import Definitions.Def_BSCvsBEC_shannon
import Definitions.Def_BSCvsBEC_expectSubset
import Definitions.Def_BSCvsBEC_Supplement_qscOut
import Definitions.Def_BSCvsBEC_Supplement_lamStarB

namespace BSCvsBEC.Supplement

/-- **Theorem 2.9 (p.11; equivalent to Theorem 2.7).** In the setting of Theorem 2.7, with
`λ*(1, 2, ρ) := ρ²`: let `X ∈ Ωⁿ` be a random variable and `Y` the output of sending `X` over `qSC_p`.
Then provided `λ ≥ λ*(α, q, ρ)`, `H_α(Y) ≥ (log q)(1 − λ)n + E_{S∼λ} H_α(X_S)` (eq. (53)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 2.9, eq. (53), p.11, in the three cases of Theorem 2.7, p.10.

**Formalization Note.** Three conjuncts, one per case of Theorem 2.7:
1. any finite alphabet `Ω` with `q = |Ω| ≥ 2`, `2 ≤ α ≤ ∞`, `λ* = lamStarA α q ρ = 1 − H_α(qSC_p)/log q`;
2. `Ω = F₂`, `1 < α < 2`, `λ* = lamStarB α ρ` (the optimal one-coordinate constant, an infimum);
3. `Ω = F₂`, `α = 1` (Shannon), `λ* = ρ²`.
In each, `ρ ∈ [0, 1]` (the range of `T_ρ`, p.6), `p = ((q − 1)/q)(1 − ρ)`, every `λ` with
`λ* ≤ λ ≤ 1`, every `n` and every pmf `P` of `X`. Entropies in bits (`renyiP`), so `log q = log₂ q`
and `log 2 = 1`. -/
theorem theorem_2_9 :
    (∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 2 ≤ Fintype.card Ω →
      ∀ (α : ENNReal), 2 ≤ α → ∀ (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      ∀ (lam : ℝ), lamStarA α (Fintype.card Ω) ρ ≤ lam → lam ≤ 1 →
      ∀ (n : ℕ) (P : (Fin n → Ω) → ℝ), BSCvsBEC.IsPMF P →
        Real.logb 2 (Fintype.card Ω) * ((1 - lam) * n) +
            BSCvsBEC.expectSubset lam n (fun S => renyiP α (BSCvsBEC.margR S P)) ≤
          renyiP α (qscOut (qscP (Fintype.card Ω) ρ) P)) ∧
    (∀ (α : ℝ), 1 < α → α < 2 → ∀ (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      ∀ (lam : ℝ), lamStarB α ρ ≤ lam → lam ≤ 1 →
      ∀ (n : ℕ) (P : (Fin n → Fin 2) → ℝ), BSCvsBEC.IsPMF P →
        (1 - lam) * n +
            BSCvsBEC.expectSubset lam n
              (fun S => renyiP (ENNReal.ofReal α) (BSCvsBEC.margR S P)) ≤
          renyiP (ENNReal.ofReal α) (qscOut (qscP 2 ρ) P)) ∧
    (∀ (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      ∀ (lam : ℝ), ρ ^ 2 ≤ lam → lam ≤ 1 →
      ∀ (n : ℕ) (P : (Fin n → Fin 2) → ℝ), BSCvsBEC.IsPMF P →
        (1 - lam) * n +
            BSCvsBEC.expectSubset lam n (fun S => renyiP 1 (BSCvsBEC.margR S P)) ≤
          renyiP 1 (qscOut (qscP 2 ρ) P)) := by sorry

end BSCvsBEC.Supplement
