-- Prove2me | Theorems.Thm_BilateralProfitLB_claim_7_3
-- name    : BilateralProfitLB.claim_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:06.329801+00:00
-- url     : https://prove2.me/theorems/159e2306-f778-4e6c-afde-40020999580e
-- title:
--   Claim 7.3 — the perturbed buyers $\mathcal D_j$ are well defined and regular
-- statement:
--   Let $K\ge1$ and $j\in\{0,1,\dots,K\}$, with $\mathcal D_0$ the baseline and $\mathcal D_j$, $j\ge1$, the perturbed instance of §7 (uniform seller on $[0,1]$, buyer with survival function $S_j$). Then $\mathcal D_j$ is a legitimate regular independent instance: there is an independent bilateral-trade environment with
--
--   1. seller and buyer supports both equal to $[0,1]$, and densities measurable, strictly positive on $[0,1]$ and integrating to $1$;
--   2. seller density $1$ on $[0,1]$ and buyer density $f_j=-S_j'$ on $[0,1]$;
--   3. buyer survival function $1-F_b(b)=S_j(b)$ for $b\in[0,1]$;
--   4. joint law equal to $\mathcal D_j$;
--   5. **regular** seller and buyer (Definition 2.2): the virtual cost $\psi(s)=s+F_s(s)/f_s(s)$ and the virtual value $\phi(b)=b-(1-F_b(b))/f_b(b)$ are nondecreasing on $[0,1]$.
--
--   This puts every instance of the construction in the class over which Theorem 7.1 quantifies.
--
--   Differences from the source:
--   - generalization: $j\in\{1,\dots,K\}$ → $j\in\{0,\dots,K\}$; reason: $j=0$ is the baseline $\mathcal D_0$, which p.50 also asserts to be regular; the statement specializes to $j\ge1$
--   - reading: "well-defined" → a probability law with the stated survival function and a buyer density strictly positive on $[0,1]$; reason: the proof shows $S_j$ strictly decreasing ($Y_j'>0$), and §2 (p.4) assumes strictly positive densities on $[0,1]$ for this class
--   - encoding: "regular" for the buyer → regularity of seller and buyer (Lean's `Environment.Regular`); reason: the uniform seller has $\psi(s)=2s$, regular as p.50 notes; this is Definition 2.2 for the instance
--   - encoding: $I_j$ unspecified endpoints → $I_j=(a_j,a_j+w)$ open; reason: $S_j=S_0$ at both endpoints, so $\mathcal D_j$ is the same distribution for any choice of endpoints
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Claim 7.3, p.50 (PDF 52); Definitions 2.1–2.2, p.4 (PDF 6)

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction
import Definitions.Def_BilateralProfitLB_Stochastic

namespace BilateralProfitLB

open MechanismDesign.BilateralTrade

/-- **Claim 7.3**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.50
(PDF 52): the buyer distribution under `𝒟_j` is well-defined and regular. Stated, for every
`K ≥ 1` and every `j ≤ K` (`j = 0` is the baseline `𝒟_0`, which p.50 also asserts to be
regular), as: there is an independent bilateral-trade environment `E` with supports
`[0, 1]`, seller density `1` on `[0, 1]` (uniform seller), buyer density `f_j = −S_j′` on
`[0, 1]`, buyer survival function `1 − F_b = S_j` on `[0, 1]`, joint law `law K j`, and both
virtual-value functions nondecreasing on `[0, 1]` (Definition 2.2).

**Formalization Note.** `Environment` requires measurable densities strictly positive on the
closed supports and integrating to `1`; so the claim includes `f_j > 0` on `[0, 1]`, i.e. that
`𝒟_j` belongs to the class of §2, p.4. The uniform seller's regularity (`ψ(s) = 2s`) is part of
`Regular`. -/
theorem claim_7_3 (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj : j ≤ K) :
    ∃ E : Environment, UnitSupport E ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, E.fS x = 1) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, E.fB b = fB K j b) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, 1 - E.cdfB b = S K j b) ∧
      E.prior = law K j ∧ E.Regular := by sorry

end BilateralProfitLB
