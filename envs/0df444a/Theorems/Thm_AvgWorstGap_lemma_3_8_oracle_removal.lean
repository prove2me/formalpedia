-- Prove2me | Theorems.Thm_AvgWorstGap_lemma_3_8_oracle_removal
-- name    : AvgWorstGap.lemma_3_8_oracle_removal
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:52:46.061485+00:00
-- url     : https://prove2.me/theorems/e75663af-5fb2-4592-8ca1-c443ae65d449
-- title:
--   Lemma 3.8 — removing the SAT oracle from pK
-- statement:
--   Suppose $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MIN}\ell\text{-}\mathrm{pKT}^{\mathrm{SAT}}\in\mathsf{prBPP}$. Then there are a polynomial $p$ and an integer $N_0\ge1$ with the following property. Let $n,m,\tau,\ell,t,b,d$ be positive integers, and let $x\in\{0,1\}^n$, $y\in\{0,1\}^m$, such that
--
--   1. $2/3<b/n^3<1$ and $2/3<d/n^3<1$;
--   2. $N_0\le n\le\tau$ and $N_0\le m\le\tau$;
--   3. $\tau\le\ell\le\tau^4$;
--   4. $t\ge2p(\tau)$.
--
--   Then
--   $$\mathrm{pK}^{p(t)}(y\mid x)\le\mathrm{pK}^{\tau,\mathrm{SAT}}_{1-1/n^3}(y\mid x)+\ell\text{-}\mathrm{pK}^{t-p(\tau),\mathrm{SAT}}_{b/n^3,(d+1)/n^3}(x)-(\ell+\tau^3)\text{-}\mathrm{pK}^{t+p(\tau),\mathrm{SAT}}_{(b-1)/n^3,(d-2)/n^3}(x)+\log p(t).$$
--
--   The lemma trades a SAT oracle for extra time. The error term is a difference of two $\ell$-$\mathrm{pK}$ values at time bounds that differ only by an additive $2p(\tau)$, and a telescoping argument in the proof of Lemma 3.4 makes it small.
--
--   **Formalization Note** The subtracted term is moved to the left-hand side, so the inequality is stated in the extended reals without subtraction.
--
--   Differences from the source:
--   - reading: "2/3 < b/n³, d/n³ < 1" and "N0 ≤ n, m ≤ τ" → both ratios in (2/3, 1); N0 ≤ n ≤ τ and N0 ≤ m ≤ τ; reason: the comma lists two quantities under one chain of inequalities; the proof uses n ≤ τ (p.25)
--   - reading: ℓ-pK_{b/n³,(d+1)/n³} with Def. 3.5's domain γ ∈ (0,1) → the same formula for every real γ, including (d+1)/n³ = 1 when d = n³ − 1; reason: the lemma's constraints allow d = n³ − 1; the formula of Def. 3.5 is used as written
--   - encoding: an inequality of the form A ≤ B − C + D → A + C ≤ B + D in EReal; reason: avoids ⊤ − ⊤; equivalent whenever the values are finite
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - encoding: the language SAT → satisfiable CNF formulas under the fixed binary encoding encCNF; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 3.8, p.24

import Mathlib
import Definitions.Def_AvgWorstGap_MildGapMINlpKT
import Definitions.Def_AvgWorstGap_SAT

namespace AvgWorstGap

open NKtLB

/-- **Lemma 3.8** (arXiv:2610.19162, version of October 30, 2026, p.24): "Suppose `Mild-Gap-MINℓ-pKT^SAT ∈ prBPP`. Then there exist a
polynomial `p` and an integer `N0 ∈ ℕ+` such that the following holds. For any
`n, m, τ, ℓ, t, b, d ∈ ℕ+` and any strings `x ∈ {0, 1}^n` and `y ∈ {0, 1}^m` satisfying the
following constraints: `2/3 < b/n³, d/n³ < 1`, `N0 ≤ n, m ≤ τ`, `τ ≤ ℓ ≤ τ⁴`, `t ≥ 2p(τ)`, we have
`pK^{p(t)}(y | x) ≤ pK^{τ,SAT}_{1−1/n³}(y | x) + ℓ-pK^{t−p(τ),SAT}_{b/n³,(d+1)/n³}(x) −
(ℓ+τ³)-pK^{t+p(τ),SAT}_{(b−1)/n³,(d−2)/n³}(x) + log p(t)`."

**Formalization Note.** `2/3 < b/n³, d/n³ < 1` is read as both ratios in `(2/3, 1)`, and
`N0 ≤ n, m ≤ τ` as `N0 ≤ n ≤ τ` and `N0 ≤ m ≤ τ`. `pK^{p(t)}` has `λ = 2/3` and no oracle. The
subtracted term is moved to the left side, so the inequality is stated in `EReal` without
subtraction (equivalent when the values are finite). `t − p(τ)` is natural subtraction, exact since
`t ≥ 2p(τ)`. `log` is `Real.logb 2`. -/
theorem lemma_3_8_oracle_removal (h : MildGapLInPrBPP SAT) :
    ∃ (p : Polynomial ℕ) (N₀ : ℕ), 1 ≤ N₀ ∧
      ∀ (n m τ ℓ t b d : ℕ), 1 ≤ n → 1 ≤ m → 1 ≤ τ → 1 ≤ ℓ → 1 ≤ t → 1 ≤ b → 1 ≤ d →
      ∀ (x y : List Bool), x.length = n → y.length = m →
        (2 / 3 : ℝ) < (b : ℝ) / (n : ℝ) ^ 3 → (b : ℝ) / (n : ℝ) ^ 3 < 1 →
        (2 / 3 : ℝ) < (d : ℝ) / (n : ℝ) ^ 3 → (d : ℝ) / (n : ℝ) ^ 3 < 1 →
        N₀ ≤ n → n ≤ τ → N₀ ≤ m → m ≤ τ →
        τ ≤ ℓ → ℓ ≤ τ ^ 4 →
        2 * p.eval τ ≤ t →
        toEReal (pK ∅ (p.eval t) (2 / 3) y x) +
            lpK SAT (t + p.eval τ) (ℓ + τ ^ 3) (((b : ℝ) - 1) / (n : ℝ) ^ 3)
              (((d : ℝ) - 2) / (n : ℝ) ^ 3) x ≤
          toEReal (pK SAT τ (1 - 1 / (n : ℝ) ^ 3) y x) +
            lpK SAT (t - p.eval τ) ℓ ((b : ℝ) / (n : ℝ) ^ 3) (((d : ℝ) + 1) / (n : ℝ) ^ 3) x +
            ((Real.logb 2 ((p.eval t : ℕ) : ℝ) : ℝ) : EReal) := by sorry

end AvgWorstGap
