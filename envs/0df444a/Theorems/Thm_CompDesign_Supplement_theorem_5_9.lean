-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_5_9
-- name    : CompDesign.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:58:19.100566+00:00
-- url     : https://prove2.me/theorems/32fa3fa6-f514-4f91-b0b0-8513e5d34eb7
-- title:
--   Theorem 5.9 — additive $v$, any nonnegative budget-feasible rule: every CCE has $\mathbb E_\mu v(S)\le2\,\mathrm{OPT}$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget and $c_i\ge0$ the private costs. The value function is additive, $v(S)=\sum_{i\in S}v_i$ with $v_i\ge0$, and $p$ is any payment rule with $p_i(S)\ge0$ and $\sum_ip_i(S)\le B$ for all $S$ (it may depend on the costs).
--
--   **Theorem 5.9.** If $\mu$ is a coarse correlated equilibrium of the game induced by $p$, then
--   $$\mathbb E_{S\sim\mu}[v(S)]\ \le\ 2\,\mathrm{OPT}.$$
--
--   This shows that the construction of Theorem 5.8 is tight for additive values.
--
--   Differences from the source: none.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 5.9, §5.5, p.43 (PDF 46)

import Mathlib
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsCCEOf
import Definitions.Def_FairShares_IsAdditive

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 5.9, §5.5, p.43 (PDF 46) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Let `v` be additive and `p` any nonnegative
budget-feasible payment rule. If `μ` is a coarse correlated equilibrium of the induced game, then
`E_{S∼μ}[v(S)] ≤ 2 OPT`.

**Formalization Note.** `p` is any function `2^N → ℝ^N` with `p_i(S) ≥ 0` and `∑_i p_i(S) ≤ B`; it may
depend on the costs. `B > 0` and `c ≥ 0` are standing. Additivity is the published
`FairShares.IsAdditive` (nonnegative item values `v_i`, `v(S) = ∑_{i∈S} v_i`). -/
theorem theorem_5_9 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv : FairShares.IsAdditive v) (hc : ∀ i, 0 ≤ c i) (p : Finset (Fin n) → Fin n → ℝ)
    (hnn : ∀ S i, 0 ≤ p S i) (hbf : ∀ S, ∑ i, p S i ≤ B)
    (μ : Finset (Fin n) → ℝ) (hμ : IsCCEOf p c μ) :
    expect μ v ≤ 2 * OPT v B c := by sorry

end CompDesign.Supplement
