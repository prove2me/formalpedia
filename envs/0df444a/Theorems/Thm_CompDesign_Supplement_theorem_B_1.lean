-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_B_1
-- name    : CompDesign.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:02:17.181315+00:00
-- url     : https://prove2.me/theorems/ea8b338e-323f-4e45-8af8-cd54634ac9ad
-- title:
--   Theorem B.1 — $\gamma$-marginal-covering rules: $\mathrm{OPT}\le(1+\kappa_\gamma(\lambda))v(S)$ at every PNE, $\kappa_\gamma(\lambda)\le\frac1{\gamma-\lambda}$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget and $c_i\ge0$ the private costs. the value function $v$ satisfies Assumption 3.1: $v(\emptyset)=0$, $v$ is monotone and submodular. A budget-share rule pays $p_i(S)=B\,y_i(S)$ ($i\in S$) with $y_i(S)\ge0$, $\sum_{i\in S}y_i(S)\le1$; it is $\gamma$-marginal-covering ($\gamma\in(0,1]$) if $y_i(S)\ge\gamma(v(S)-v(S\setminus\{i\}))/v(S)$ whenever $v(S)>0$, $i\in S$.
--
--   **Theorem B.1 (PoA bound for marginal-covering rules).** Let $\lambda=\max_ic_i/B<\gamma$. For every pure Nash equilibrium $S$ of a $\gamma$-marginal-covering budget-share rule,
--   $$\mathrm{OPT}\ \le\ (1+\kappa_\gamma(\lambda))\,v(S),\qquad \kappa_\gamma(\lambda)=\max\Big\{\sum_i\frac{x_i}{\gamma-x_i}:0\le x_i\le\lambda,\ \sum_ix_i\le1\Big\}.$$
--   In particular, $\kappa_\gamma(\lambda)\le1/(\gamma-\lambda)$, so $\mathrm{PoA}_{\mathrm{PNE}}\le1+1/(\gamma-\lambda)$.
--
--   This extends Theorem 5.1 (the case $\gamma=1$, $p=p^{mc}$) to every marginal-covering budget-share rule; it does not assert that a pure equilibrium exists.
--
--   Differences from the source:
--   - encoding: λ = max_i c_i/B → any l with 0 ≤ l < γ and c_i ≤ l·B for every i; reason: κ_γ is nondecreasing in l, so the case l = max_i c_i/B is the paper's statement
--   - encoding: OPT ≤ ρ·(value) for every equilibrium (PoA ≤ ρ) → OPT ≤ ρ · E_μ v(S) (or ρ·v(S)); reason: equivalent to the ratio bound with the +∞ convention of (5), without division
--   - encoding: "in particular, PoA_PNE ≤ 1 + 1/(γ − λ)" → the clause κ_γ(l) ≤ 1/(γ − l); reason: with the first clause it gives the stated bound
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem B.1, App. B.1, p.70 (PDF 73)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsPNEOf
import Definitions.Def_CompDesign_Supplement_budgetSharePay
import Definitions.Def_CompDesign_Supplement_kappaGamma

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem B.1 (PoA bound for marginal-covering rules), App. B.1, p.70 (PDF 73) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Consider
any `γ`-marginal-covering budget-share rule with shares `y_i(S)` and `λ = max_i c_i/B < γ`. For every
pure Nash equilibrium `S`, `OPT ≤ (1 + κ_γ(λ)) v(S)`, where
`κ_γ(λ) = max{∑_i x_i/(γ − x_i) : 0 ≤ x_i ≤ λ, ∑_i x_i ≤ 1}`. In particular,
`PoA_PNE ≤ 1 + 1/(γ − λ)`.

**Formalization Note.** `γ ∈ (0,1]` (Definition 3.4); `λ` enters as any `l` with `0 ≤ l < γ` and
`c_i ≤ l B` (`κ_γ` is nondecreasing in `l`). The rule is `p_i(S) = B y_i(S)` for `i ∈ S`, `0`
otherwise, and the pure Nash equilibrium is Definition 3.1 for it. "In particular" is the clause
`κ_γ(λ) ≤ 1/(γ − λ)`. Assumption 3.1 is standing (the proof is "analogous to Theorem 5.1"), as are
`B > 0` and `c ≥ 0`. -/
theorem theorem_B_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (l : ℝ) (hl0 : 0 ≤ l) (hlγ : l < γ)
    (hcl : ∀ i, c i ≤ l * B) (y : Finset (Fin n) → Fin n → ℝ) (hy : IsBudgetShare y)
    (hcov : IsMarginalCovering γ v y) :
    (∀ S : Finset (Fin n), IsPNEOf (budgetSharePay B y) c S →
      OPT v B c ≤ (1 + kappaGamma γ l) * v S) ∧ kappaGamma γ l ≤ 1 / (γ - l) := by sorry

end CompDesign.Supplement
