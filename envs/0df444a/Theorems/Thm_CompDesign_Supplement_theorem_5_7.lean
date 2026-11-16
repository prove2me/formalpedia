-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_5_7
-- name    : CompDesign.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:57:15.453384+00:00
-- url     : https://prove2.me/theorems/0113afc4-24ee-4123-bdd6-46eba222e1b2
-- title:
--   Theorem 5.7 — additive $v$: every CCE of $\Gamma^{mc}$ has $\mathrm{OPT}\le(1+\kappa(\lambda))\,\mathbb E_\mu v(S)$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget and $c_i\ge0$ the private costs. The value function is additive, $v(S)=\sum_{i\in S}v_i$ with $v_i\ge0$; $\kappa(\lambda)=\max\{\sum_ix_i/(1-x_i):0\le x_i\le\lambda,\ \sum_ix_i\le1\}$ is the cost concentration term (20).
--
--   **Theorem 5.7 (CCE PoA bound for additive valuations).** Let $\lambda=\max_ic_i/B<1$. Any coarse correlated equilibrium $\mu$ of $\Gamma^{mc}$ satisfies
--   $$\mathrm{OPT}\ \le\ (1+\kappa(\lambda))\,\mathbb E_{S\sim\mu}[v(S)].$$
--   As a result, $\mathrm{PoA}_{\mathrm{CCE}}\le1+\kappa(\lambda)$.
--
--   For additive values the coarse correlated equilibria of $\Gamma^{mc}$ achieve the same tight bound as its pure equilibria (Theorem 5.1).
--
--   Differences from the source:
--   - encoding: λ = max_i c_i/B → any l with 0 ≤ l < 1 and c_i ≤ l·B for every i; reason: κ is nondecreasing in l, so the case l = max_i c_i/B is the paper's statement
--   - encoding: OPT ≤ ρ·(value) for every equilibrium (PoA ≤ ρ) → OPT ≤ ρ · E_μ v(S) (or ρ·v(S)); reason: equivalent to the ratio bound with the +∞ convention of (5), without division
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 5.7, §5.4.1, p.40 (PDF 43)

import Mathlib
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_kappa
import Definitions.Def_CompDesign_Supplement_IsCCEOf
import Definitions.Def_FairShares_IsAdditive

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 5.7 (CCE PoA bound for additive valuations), §5.4.1, p.40 (PDF 43) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Suppose
that `v` is additive and `λ < 1`. Any coarse correlated equilibrium `μ` of `Γ^mc` satisfies
`OPT ≤ (1 + κ(λ)) E_{S∼μ}[v(S)]`. As a result, `PoA_CCE ≤ 1 + κ(λ)`.

**Formalization Note.** `κ` is the published `CompDesign.kappa` (20). `λ` enters as any `l` with
`0 ≤ l < 1` and `c_i ≤ l B`; `κ` is nondecreasing in `l`. Additive means `v(S) = ∑_{i∈S} v_i` with
`v_i ≥ 0`. `B > 0` and `c ≥ 0` are standing. Additivity is the published
`FairShares.IsAdditive` (nonnegative item values `v_i`, `v(S) = ∑_{i∈S} v_i`). -/
theorem theorem_5_7 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv : FairShares.IsAdditive v) (hc : ∀ i, 0 ≤ c i) (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1)
    (hcl : ∀ i, c i ≤ l * B) (μ : Finset (Fin n) → ℝ) (hμ : IsCCEOf (mcPay v B) c μ) :
    OPT v B c ≤ (1 + CompDesign.kappa l) * expect μ v := by sorry

end CompDesign.Supplement
