-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_7_2
-- name    : CompDesign.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:59:48.759339+00:00
-- url     : https://prove2.me/theorems/083b4a2b-858d-487d-95b5-489d0faa831b
-- title:
--   Theorem 7.2 — threshold-prize rule: $\mathbb E[v(S)]\ge\mathrm{OPT}/(2(\lceil\log_2m\rceil+1))$ for subadditive $v$
-- statement:
--   A single agent has actions $A=\{1,\dots,m\}$ with costs $0<c_e\le B$; the value function $v$ is normalized, monotone and subadditive ($v(S\cup S')\le v(S)+v(S')$). The randomized threshold-prize rule draws $r\in\{0,\dots,L\}$ uniformly, $L=\lceil\log_2m\rceil$, announces it and pays $p_r(S)=B$ if $v(S)\ge v(A)/2^r$ and $0$ otherwise; in branch $r$ the agent plays a platform-favoring best response $S_r$.
--
--   **Theorem 7.2.** For every choice of platform-favoring best responses $S_0,\dots,S_L$,
--   $$\mathbb E[v(S)]\ =\ \frac1{L+1}\sum_{r=0}^Lv(S_r)\ \ge\ \frac{1}{2(\lceil\log_2m\rceil+1)}\,\mathrm{OPT}.$$
--
--   Randomization over a geometric grid of thresholds overcomes the $\Omega(m)$ barrier of deterministic rules (Theorem 7.1).
--
--   Differences from the source:
--   - encoding: ⌈log₂ m⌉ → Nat.clog 2 m; reason: equal for m ≥ 1; at m = 0 both sides of the bound are 0
--   - encoding: E[v(S)] under the platform-favoring best response of each branch → (1/(L+1)) ∑_{r=0}^{L} v(S_r) for every choice of platform-favoring best responses S_r; reason: the uniform expectation over the announced branches; ties among best responses are left to the adversary
--   - encoding: costs c_e ≤ B → 0 < c_e ≤ B; reason: §7.1 takes costs positive (p.52)
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 7.2, §7.1.2, p.54 (PDF 57)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_BudgetClock_Subadditive_Setting
import Definitions.Def_CompDesign_Supplement_IsPFBestResponse
import Definitions.Def_CompDesign_Supplement_thresholdPay

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 7.2, §7.1.2, p.54 (PDF 57) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Assume that `v` is normalized, monotone, and
subadditive. Suppose further that `c_e ≤ B` for all actions `e ∈ A`. The randomized threshold-prize
rule satisfies `E[v(S)] ≥ OPT/(2(⌈log₂ m⌉ + 1))`.

**Formalization Note.** `A = Fin m`; costs are positive (§7.1, p.52). `⌈log₂ m⌉` is `Nat.clog 2 m`
(equal for `m ≥ 1`; at `m = 0` both sides are `0`). The rule draws `r ∈ {0, …, L}` uniformly and
plays `thresholdPay v B r`; the agent plays a platform-favoring best response `S_r` in branch `r`,
and the statement holds for every choice of the `S_r`, with `E[v(S)] = (1/(L+1)) ∑_r v(S_r)`.
Subadditivity is the published `BudgetClock.Subadditive.IsSubadditive` (Definition 6.2). -/
theorem theorem_7_2 {m : ℕ} (v : Finset (Fin m) → ℝ) (B : ℝ) (c : Fin m → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hsub : BudgetClock.Subadditive.IsSubadditive v)
    (hc : ∀ e, 0 < c e ∧ c e ≤ B) (S : ℕ → Finset (Fin m))
    (hS : ∀ r, r ≤ Nat.clog 2 m → IsPFBestResponse (thresholdPay v B r) v c (S r)) :
    OPT v B c / (2 * ((Nat.clog 2 m : ℝ) + 1)) ≤
      (∑ r ∈ Finset.range (Nat.clog 2 m + 1), v (S r)) / ((Nat.clog 2 m : ℝ) + 1) := by sorry

end CompDesign.Supplement
