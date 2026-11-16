-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_5_8
-- name    : CompDesign.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:57:52.71059+00:00
-- url     : https://prove2.me/theorems/112d027c-a263-4be3-808f-9ea96ffa1af8
-- title:
--   Theorem 5.8 — two-agent additive instances with a CCE of $\Gamma^{mc}$ and $\mathrm{OPT}/\mathbb E_\mu v(S)\le\frac12+\epsilon$
-- statement:
--   **Theorem 5.8 (Two-agent sharpness construction).** For every $\epsilon>0$ there are an additive value function $v$ on two agents, a budget $B>0$, costs $c_i\ge0$ and a coarse correlated equilibrium $\mu$ of the marginal-contribution game with $\mathbb E_{S\sim\mu}[v(S)]>0$ and
--   $$\frac{\mathrm{OPT}}{\mathbb E_{S\sim\mu}[v(S)]}\ \le\ \frac12+\epsilon.\qquad(46)$$
--
--   So the price of stability of coarse correlated equilibria can be arbitrarily close to $1/2$: a correlated outcome may beat the full-information benchmark by placing mass on cost-infeasible sets.
--
--   Differences from the source:
--   - encoding: OPT / E_μ v(S) ≤ 1/2 + ϵ → 0 < E_μ v(S) ∧ OPT ≤ (1/2 + ϵ)·E_μ v(S); reason: the positivity makes (46) a genuine ratio
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 5.8, §5.5, p.41 (PDF 44)

import Mathlib
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsCCEOf
import Definitions.Def_FairShares_IsAdditive

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 5.8 (Two-agent sharpness construction), §5.5, p.41 (PDF 44) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). For every
`ϵ > 0`, there is a two-agent instance with an additive value function and a coarse correlated
equilibrium `μ` of the marginal-contribution game such that `OPT / E_{S∼μ} v(S) ≤ 1/2 + ϵ` (46).

**Formalization Note.** The instance is `(v, B, c)` on `Fin 2` with `B > 0` and `c ≥ 0`. The ratio
is written `OPT ≤ (1/2 + ϵ) E_μ v(S)` together with `E_μ v(S) > 0`, so that (46) is a genuine ratio. Additivity is the published
`FairShares.IsAdditive` (nonnegative item values `v_i`, `v(S) = ∑_{i∈S} v_i`). -/
theorem theorem_5_8 (ε : ℝ) (hε : 0 < ε) :
    ∃ (v : Finset (Fin 2) → ℝ) (B : ℝ) (c : Fin 2 → ℝ) (μ : Finset (Fin 2) → ℝ),
      FairShares.IsAdditive v ∧ 0 < B ∧ (∀ i, 0 ≤ c i) ∧ IsCCEOf (mcPay v B) c μ ∧ 0 < expect μ v ∧
      OPT v B c ≤ (1 / 2 + ε) * expect μ v := by sorry

end CompDesign.Supplement
