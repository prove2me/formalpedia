-- Prove2me | Theorems.Thm_DynSort_Supplement_theorem_2
-- name    : DynSort.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:41:08.032189+00:00
-- url     : https://prove2.me/theorems/d572b3b7-c05d-4720-afb1-b1ea930dfca4
-- title:
--   Theorem 2 — recourse lower bound $\Omega(\log n/(\log C+\sqrt{\log n}))$ for $C$-competitive fully dynamic sorting
-- statement:
--   Fully dynamic sorting on an array of $n$ cells: real values are inserted and deleted online, at most $n$ are present at any time, and a deterministic online algorithm maintains an arrangement whose cost $\mathrm{cost}(S)=\sum_j|x_{j+1}-x_j|$ (stored values $S$ read left to right) it compares with $\mathrm{OPT}(S)=\max S-\min S$. The algorithm is **$C$-competitive** if $\mathrm{cost}(S)\le C\cdot\mathrm{OPT}(S)$ after every update, and has **amortized recourse $\rho$** if on every update sequence $\sigma$ the total number of element moves is at most $\rho|\sigma|$.
--
--   There are constants $c>0$, $\kappa>0$ and $N_0$ such that for every $n\ge N_0$, every real $C$ with $1\le C\le cn$ and every deterministic $C$-competitive algorithm on $n$ cells with amortized recourse $\rho$,
--   $$\rho\ \ge\ \kappa\,\frac{\log n}{\log C+\sqrt{\log n}}.$$
--
--   In particular an $O(\mathrm{polylog}\,n)$-competitive algorithm needs $\Omega(\sqrt{\log n})$ amortized recourse, and an $O(1)$-competitive one needs $\Omega(\sqrt{\log n})$ as well, so the polylogarithmic recourse of Theorem 1 is necessary up to the exponent.
--
--   Differences from the source:
--   - encoding: deterministic C-competitive algorithm for fully dynamic sorting with amortized recourse ρ → alg : OnlineAlg n with, for every valid σ, Legal, cost ≤ C·OPT of the stored elements and totalRecourse ≤ ρ·|σ|; reason: the §2 definitions in the published model, the guarantee shape of Theorem 1; σ ranges over all valid sequences, so the guarantee holds after every update
--   - encoding: 1 ≤ C ≤ O(n), pinned on p.27 as C ≤ cn for some constant c → ∃ c > 0 chosen before n; ∀ real C with 1 ≤ C ≤ c·n; reason: the paper's own clarification; C may depend on n
--   - encoding: ρ = Ω(log n / (log C + √log n)) → ∃ κ > 0, ∃ N₀, ∀ n ≥ N₀: κ·log n / (log C + √(log n)) ≤ ρ; reason: one constant and a threshold chosen before n; log is Real.log (a change of base changes only κ); for n ≥ 2 and C ≥ 1 the denominator is positive
--   - encoding: an array of size n holding at most n elements → OnlineAlg n with Valid n; reason: the setting of Theorem 1, which Theorem 2 complements
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Theorem 2, §6, p.27 (PDF p.29), with the clarification 'C ≤ cn for some constant c' on the same page; also stated in §1.1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_DynSort_cost
import Definitions.Def_DynSort_OnlineAlg

namespace DynSort.Supplement

open DynSort

/-- **Theorem 2**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §6, p.27 (PDF p.29; also §1.1, p.1): "Let 1 ≤ C ≤ O(n). Any deterministic
C-competitive algorithm for fully dynamic sorting with amortized recourse ρ satisfies
ρ = Ω(log n / (log C + √log n)). We clarify that in Theorem 2, the condition C ≤ O(n) means that
C ≤ cn for some constant c."

**Formalization Note.** Constants `c > 0` (in `C ≤ c·n`), `κ > 0` (the `Ω`) and a threshold
`N₀` are chosen before `n`. For every `n ≥ N₀`, every real `C ∈ [1, c·n]`, every online
algorithm on exactly `n` cells and every real `ρ`: if on every valid update sequence `σ`
(arbitrary reals, duplicates, deletions, at most `n` elements present) the arrangement after `σ`
is legal with cost at most `C·opt` and the total recourse over `σ` is at most `ρ·|σ|` (the
guarantee shape of Theorem 1), then `ρ ≥ κ·log n / (log C + √(log n))`. `log` is `Real.log`;
for `n ≥ 2` and `C ≥ 1` the denominator is positive. -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ C : ℝ, 1 ≤ C → C ≤ c * n → ∀ alg : OnlineAlg n, ∀ ρ : ℝ,
        (∀ σ : List Update, Valid n σ →
          Legal n σ (alg σ) ∧
          cost (seq σ (alg σ)) ≤ C * opt (seq σ (alg σ)) ∧
          (totalRecourse alg σ : ℝ) ≤ ρ * σ.length) →
        κ * Real.log n / (Real.log C + Real.sqrt (Real.log n)) ≤ ρ := by sorry

end DynSort.Supplement
