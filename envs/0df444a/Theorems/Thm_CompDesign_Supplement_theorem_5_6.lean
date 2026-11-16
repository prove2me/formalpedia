-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_5_6
-- name    : CompDesign.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:56:43.697015+00:00
-- url     : https://prove2.me/theorems/da605764-e7f9-4859-8f9a-4679895c1e6d
-- title:
--   Theorem 5.6 — CCEs of 1-marginal-covering budget-share rules (incl. $\Gamma^{mc}$, Shapley): $\mathrm{OPT}\le\frac2{1-2\lambda}\mathbb E_\mu v(S)$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget and $c_i\ge0$ the private costs. the value function $v$ satisfies Assumption 3.1: $v(\emptyset)=0$, $v$ is monotone and submodular. A budget-share rule pays $p_i(S)=B\,y_i(S)$ to $i\in S$ (and $0$ otherwise) with shares $y_i(S)\ge0$, $\sum_{i\in S}y_i(S)\le1$; it is 1-marginal-covering if $y_i(S)\ge(v(S)-v(S\setminus\{i\}))/v(S)$ whenever $v(S)>0$ and $i\in S$.
--
--   **Theorem 5.6 (Improved CCE PoA bound).** Let $\lambda=\max_ic_i/B<1/2$. If $\mu$ is a coarse correlated equilibrium of a 1-marginal-covering budget-share rule, then
--   $$\mathrm{OPT}\ \le\ \frac{2}{1-2\lambda}\,\mathbb E_{S\sim\mu}[v(S)].$$
--   As a result, $\mathrm{PoA}_{\mathrm{CCE}}\le2/(1-2\lambda)=2+o_\lambda(1)$. In particular, this bound applies to $\Gamma^{mc}$ and to normalized Shapley payments.
--
--   The three clauses of the formal statement are the general bound, the bound for every coarse correlated equilibrium of $\Gamma^{mc}$ and the bound for every coarse correlated equilibrium of the Shapley rule (7).
--
--   Differences from the source:
--   - encoding: λ = max_i c_i/B → any l with 0 ≤ l < 1/2 and c_i ≤ l·B for every i; reason: the bound is nondecreasing in l, so the case l = max_i c_i/B is the paper's statement
--   - encoding: OPT ≤ ρ·(value) for every equilibrium (PoA ≤ ρ) → OPT ≤ ρ · E_μ v(S) (or ρ·v(S)); reason: equivalent to the ratio bound with the +∞ convention of (5), without division
--   - encoding: "in particular, this bound applies to Γ^mc and to normalized Shapley payments" → two further conjuncts: the same bound for every CCE of mcPay v B and of shapleyPay v B; reason: the instances are stated explicitly rather than through the 1-marginal-covering shares (Definition 3.4, Lemma 3.1)
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 5.6, §5.4, p.38 (PDF 41)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsCCEOf
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesign_Supplement_budgetSharePay
import Definitions.Def_CompDesign_Supplement_shapleyPay

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 5.6 (Improved CCE PoA bound), §5.4, p.38 (PDF 41) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Let `v` be monotone and
submodular, and let `μ` be a coarse correlated equilibrium of a 1-marginal-covering budget-share rule.
Then, if `λ < 1/2`, `OPT ≤ 2/(1 − 2λ) E_{S∼μ}[v(S)]`. As a result, `PoA_CCE ≤ 2/(1 − 2λ)`.

**Formalization Note.** The rule is any budget-share rule `p_i(S) = B y_i(S)` (`i ∈ S`), `0` otherwise
(Definition 3.3), whose shares `y` are 1-marginal-covering (Definition 3.4). `λ` enters as any `l`
with `0 ≤ l < 1/2` and `c_i ≤ l B`. The sentence "in particular, this bound applies to `Γ^mc` and to
normalized Shapley payments" is stated as two further conjuncts, for every coarse correlated
equilibrium of `p^mc` (the published `CompDesignBFM.mcPay`) and of `p^Sh` (7). Assumption 3.1,
`B > 0` and `c ≥ 0` are standing. -/
theorem theorem_5_6 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1 / 2) (hcl : ∀ i, c i ≤ l * B) :
    (∀ y : Finset (Fin n) → Fin n → ℝ, IsBudgetShare y → IsMarginalCovering 1 v y →
      ∀ μ : Finset (Fin n) → ℝ, IsCCEOf (budgetSharePay B y) c μ →
        OPT v B c ≤ 2 / (1 - 2 * l) * expect μ v) ∧
    (∀ μ : Finset (Fin n) → ℝ, IsCCEOf (mcPay v B) c μ →
      OPT v B c ≤ 2 / (1 - 2 * l) * expect μ v) ∧
    (∀ μ : Finset (Fin n) → ℝ, IsCCEOf (shapleyPay v B) c μ →
      OPT v B c ≤ 2 / (1 - 2 * l) * expect μ v) := by sorry

end CompDesign.Supplement
