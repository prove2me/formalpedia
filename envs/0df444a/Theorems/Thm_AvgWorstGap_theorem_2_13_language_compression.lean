-- Prove2me | Theorems.Thm_AvgWorstGap_theorem_2_13_language_compression
-- name    : AvgWorstGap.theorem_2_13_language_compression
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:50:07.574876+00:00
-- url     : https://prove2.me/theorems/33605e57-e6f0-4f6f-b985-6e1ce82ff149
-- title:
--   Theorem 2.13 — language compression for pnKt (cited from [HLO26])
-- statement:
--   There is a polynomial $p_{\mathrm{LC}}$ with the following property. Let $A=\{A_n\}_{n\in\mathbb N}$ be any family of sets with $A_n\subseteq\{0,1\}^n$. Then for every $n$ and every $x\in A_n$,
--   $$\mathrm{pnK}^{p_{\mathrm{LC}}(n),A_n}(x)\le\log|A_n|+\log p_{\mathrm{LC}}(n).$$
--   Here $\mathrm{pnK}$ has $\lambda=2/3$ and oracle access to the set $A_n$.
--
--   Every member of a set can be described, nondeterministically and with oracle access to the set, by about $\log|A_n|$ bits. The paper cites this result from Hu, Lu and Oliveira [HLO26] and uses it in the proof of Lemma 3.4 to compress NP witnesses.
--
--   Differences from the source:
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - reading: programs Π for nK^t and pnK^t → single machine-advice pairs (M, α) run with the guess tape; reason: the composition model of p.13 has no guess tape; the nondeterministic output is defined for the pair model of p.12
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Theorem 2.13, p.16

import Mathlib
import Definitions.Def_AvgWorstGap_Kt
import Definitions.Def_AvgWorstGap_pnK

namespace AvgWorstGap

open NKtLB

/-- **Theorem 2.13 (Language Compression for pnKt [HLO26])** (cited; arXiv:2610.19162, version of October 30, 2026, p.16):
"There is a polynomial `pLC(·)` such that for every set `A := {An ⊆ {0, 1}^n}n∈ℕ`, and for all
`n ∈ ℕ` and `x ∈ An`, `pnK^{pLC(n),An}(x) ≤ log |An| + log pLC(n)`."

**Formalization Note.** `pnK` with `λ = 2/3` (omitted in the paper), oracle the finite set `A_n`,
no condition. `log` is `Real.logb 2`; comparison in `EReal`. The polynomial comes before the set
family. -/
theorem theorem_2_13_language_compression :
    ∃ pLC : Polynomial ℕ, ∀ A : ℕ → Set (List Bool), (∀ n, ∀ z ∈ A n, z.length = n) →
      ∀ n : ℕ, ∀ x ∈ A n,
        toEReal (pnK (A n) (pLC.eval n) (2 / 3) x []) ≤
          ((Real.logb 2 ((A n).ncard : ℝ) + Real.logb 2 ((pLC.eval n : ℕ) : ℝ) : ℝ) : EReal) := by sorry

end AvgWorstGap
