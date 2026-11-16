-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_5_5
-- name    : CompDesign.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:56:07.266063+00:00
-- url     : https://prove2.me/theorems/84c21cca-587d-4f07-950c-bcbfab05090e
-- title:
--   Theorem 5.5 — every CCE of $\Gamma^{mc}$ has $\mathrm{OPT}\le(2+\frac1{1-\lambda})\,\mathbb E_\mu v(S)$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget and $c_i\ge0$ the private costs. the value function $v$ satisfies Assumption 3.1: $v(\emptyset)=0$, $v$ is monotone and submodular. $\Gamma^{mc}$ is the game induced by the marginal-contribution rule (8), and $\mathrm{OPT}=\max\{v(T):\sum_{i\in T}c_i\le B\}$.
--
--   **Theorem 5.5 (PoA bound for CCEs).** Let $\lambda=\max_ic_i/B<1$. For any coarse correlated equilibrium $\mu\in\Delta(2^N)$ of $\Gamma^{mc}$,
--   $$\mathrm{OPT}\ \le\ \Big(2+\frac1{1-\lambda}\Big)\,\mathbb E_{S\sim\mu}[v(S)].$$
--   As a result, $\mathrm{PoA}_{\mathrm{CCE}}\le2+1/(1-\lambda)$.
--
--   The marginal-contribution rule keeps a constant price of anarchy for the larger, efficiently learnable class of coarse correlated equilibria.
--
--   Differences from the source:
--   - encoding: λ = max_i c_i/B → any l with 0 ≤ l < 1 and c_i ≤ l·B for every i; reason: the bound is nondecreasing in l, so the case l = max_i c_i/B is the paper's statement
--   - encoding: OPT ≤ ρ·(value) for every equilibrium (PoA ≤ ρ) → OPT ≤ ρ · E_μ v(S) (or ρ·v(S)); reason: equivalent to the ratio bound with the +∞ convention of (5), without division
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 5.5, §5.4, p.35 (PDF 38)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsCCEOf

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 5.5 (PoA bound for CCEs), §5.4, p.35 (PDF 38) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Let `λ = max_i c_i/B < 1`.
For any coarse correlated equilibrium `μ ∈ Δ(2^N)` of `Γ^mc`,
`OPT ≤ (2 + 1/(1 − λ)) E_{S∼μ}[v(S)]`. As a result, `PoA_CCE ≤ 2 + 1/(1 − λ)`.

**Formalization Note.** `λ` enters as any `l` with `0 ≤ l < 1` and `c_i ≤ l B`; the bound is
nondecreasing in `l`, so the case `l = max_i c_i/B` is the paper's. The coarse correlated
equilibrium is Definition 3.2 (`ε = 0`) for the rule `p^mc` (the published `CompDesignBFM.mcPay`).
Assumption 3.1, `B > 0` and `c ≥ 0` are the standing assumptions. -/
theorem theorem_5_5 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) (hcl : ∀ i, c i ≤ l * B)
    (μ : Finset (Fin n) → ℝ) (hμ : IsCCEOf (mcPay v B) c μ) :
    OPT v B c ≤ (2 + 1 / (1 - l)) * expect μ v := by sorry

end CompDesign.Supplement
