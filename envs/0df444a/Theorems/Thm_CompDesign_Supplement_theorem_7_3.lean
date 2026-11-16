-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_7_3
-- name    : CompDesign.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:00:37.658294+00:00
-- url     : https://prove2.me/theorems/f1813ac8-2d05-49ab-a824-84b7b315e370
-- title:
--   Theorem 7.3 — large market $c_e\le\lambda B$: threshold-prize rule with $L_\lambda=\lceil\log_2q\rceil$, factor $O(\log(m\lambda+2))$
-- statement:
--   In the setting of Theorem 7.2, suppose instead that $0<c_e\le\lambda B$ for a known $\lambda\in(0,1]$. Let $k=\min\{m,\lfloor1/\lambda\rfloor\}$, $q=\lceil m/k\rceil$ and $L_\lambda=\lceil\log_2q\rceil$; the threshold-prize rule draws $r\in\{0,\dots,L_\lambda\}$ uniformly.
--
--   **Theorem 7.3.** For every choice of platform-favoring best responses $S_r$,
--   $$\mathbb E[v(S)]\ =\ \frac1{L_\lambda+1}\sum_{r=0}^{L_\lambda}v(S_r)\ \ge\ \frac1{2(L_\lambda+1)}\,\mathrm{OPT}.$$
--   In particular, the approximation factor is $O(\log q+1)=O(\log(m\lambda+2))$: there is an absolute constant $C>0$ with $2(L_\lambda+1)\le C(\log q+1)$ and $2(L_\lambda+1)\le C\log(m\lambda+2)$ for all $m\ge1$ and $\lambda\in(0,1]$.
--
--   When every action is cheap relative to the budget, the logarithmic factor depends only on $m\lambda$.
--
--   Differences from the source:
--   - reading: O(log q + 1) = O(log(mλ + 2)) → ∃ C > 0 such that for all m ≥ 1 and λ ∈ (0,1]: 2(L_λ+1) ≤ C(log q + 1) and 2(L_λ+1) ≤ C·log(mλ + 2); reason: the O-notation with one absolute constant, uniform in m and λ
--   - encoding: ⌈log₂ q⌉, q = ⌈m/min{m, ⌊1/λ⌋}⌉ → Nat.clog 2 (blockCount m l); reason: the same quantities; at m = 0 the bound is trivial
--   - encoding: E[v(S)] → (1/(L_λ+1)) ∑_r v(S_r) for every choice of platform-favoring best responses; reason: as in Theorem 7.2
--   - encoding: costs c_e ≤ λB → 0 < c_e ≤ λ·B; reason: §7.1 takes costs positive (p.52)
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 7.3, §7.1.2, p.55 (PDF 58)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_BudgetClock_Subadditive_Setting
import Definitions.Def_CompDesign_Supplement_IsPFBestResponse
import Definitions.Def_CompDesign_Supplement_thresholdPay
import Definitions.Def_CompDesign_Supplement_blockCount

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 7.3, §7.1.2, p.55 (PDF 58) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Assume that `v` is normalized, monotone, and
subadditive. Suppose further that `c_e ≤ λB` for all `e ∈ A`. The randomized threshold-prize rule
with `L_λ = ⌈log₂ q⌉` satisfies `E[v(S)] ≥ OPT/(2(L_λ + 1))`, where `q = ⌈m/min{m, ⌊1/λ⌋}⌉`. In
particular, the approximation factor is `O(log q + 1) = O(log(mλ + 2))`.

**Formalization Note.** `λ ∈ (0,1]` is `l` (p.55), `q` is `blockCount m l`, `L_λ = Nat.clog 2 q`.
The rule draws `r ∈ {0, …, L_λ}` uniformly and plays `thresholdPay v B r`; the bound holds for every
choice of platform-favoring best responses `S_r`. The `O`-clauses are read with one absolute constant
`C > 0`: `2(L_λ + 1) ≤ C (log q + 1)` and `2(L_λ + 1) ≤ C log(mλ + 2)` for all `m ≥ 1` and
`λ ∈ (0,1]`. Costs are positive (§7.1). -/
theorem theorem_7_3 :
    (∀ {m : ℕ} (v : Finset (Fin m) → ℝ) (B : ℝ) (c : Fin m → ℝ) (l : ℝ), 0 < B → v ∅ = 0 →
      IsMonotoneSF v → BudgetClock.Subadditive.IsSubadditive v → 0 < l → l ≤ 1 →
      (∀ e, 0 < c e ∧ c e ≤ l * B) → ∀ S : ℕ → Finset (Fin m),
      (∀ r, r ≤ Nat.clog 2 (blockCount m l) → IsPFBestResponse (thresholdPay v B r) v c (S r)) →
      OPT v B c / (2 * ((Nat.clog 2 (blockCount m l) : ℝ) + 1)) ≤
        (∑ r ∈ Finset.range (Nat.clog 2 (blockCount m l) + 1), v (S r)) /
          ((Nat.clog 2 (blockCount m l) : ℝ) + 1)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ l : ℝ, 0 < l → l ≤ 1 →
      2 * ((Nat.clog 2 (blockCount m l) : ℝ) + 1) ≤ C * (Real.log (blockCount m l) + 1) ∧
      2 * ((Nat.clog 2 (blockCount m l) : ℝ) + 1) ≤ C * Real.log (m * l + 2) := by sorry

end CompDesign.Supplement
