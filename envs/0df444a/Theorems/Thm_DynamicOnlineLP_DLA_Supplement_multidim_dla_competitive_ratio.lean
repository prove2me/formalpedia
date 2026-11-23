-- Prove2me | Theorems.Thm_DynamicOnlineLP_DLA_Supplement_multidim_dla_competitive_ratio
-- name    : DynamicOnlineLP.DLA.Supplement.multidim_dla_competitive_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:12:42.84934+00:00
-- url     : https://prove2.me/theorems/32296474-72c9-4b7a-92fc-4e9622fd4cb4
-- title:
--   Theorem 3 — the multidimensional dynamic learning algorithm is 1 − O(ε) competitive when B ≥ Ω(m log(nk/ε)/ε²)
-- statement:
--   In the general online LP (3), $n\ge1$ arrivals each offer $k\ge1$ options and share $m\ge1$ resources. Arrival $t$ has a reward vector $f_t\ge0$ in $\mathbb R^k$ and consumption vectors $g_{it}\in[0,1]^k$, and a decision is a vector in $K=\{x\ge0:e^{\top}x\le1\}$. For a right-hand side $b\ge0$,
--
--   $$\mathrm{OPT}=\max\Big\{\sum_{t=1}^nf_t^{\top}x_t:\ \sum_{t=1}^ng_{it}^{\top}x_t\le b_i\ (i=1,\dots,m),\ \ x_t\in K\Big\}.$$
--
--   The $n$ blocks $(f_t,g_{1t},\dots,g_{mt})$ arrive in a uniformly random order $\sigma$, and $n$ is known in advance. The input is in general position: for every $p\in\mathbb R^m$, at most $m$ arrivals have a nonunique maximizer among the score $0$ of rejection and the surpluses $f_{tj}-\sum_ip_ig_{itj}$.
--
--   Fix a real $\varepsilon>0$ and put $E=\max\{1,\lceil\log_2(1/\varepsilon)\rceil\}$, $\delta=2^{-E}$ and $\ell_r=\lceil2^r\delta n\rceil$. The multidimensional dynamic learning algorithm rejects the first $\ell_0$ arrivals. After time $\ell_r$ and until time $\ell_{r+1}$ it proposes the surplus-maximizing vector at an optimal dual resource price of the program on the first $\ell_r$ blocks with capacities $(1-\delta\sqrt{n/\ell_r})\frac{\ell_r}{n}b$. If $\delta n<1$ it proposes a best-reward option from the start. It executes a proposal only if the remaining resources allow it. Write $x_t$ for the executed decisions.
--
--   There are absolute constants $C_1,C_2>0$, independent of $m,n,k,\varepsilon$, the data, the selection of dual prices and the tie-breaking, such that whenever
--
--   $$B=\min_ib_i\ \ge\ \frac{C_1\,m\log(nk/\varepsilon)}{\varepsilon^2},$$
--
--   one has
--
--   $$\mathbb E_\sigma\Big[\sum_{t=1}^nf_{\sigma(t)}^{\top}x_t\Big]\ \ge\ (1-C_2\varepsilon)\,\mathrm{OPT}.$$
--
--   This is a companion theorem of the mission, not used in the proof of the scalar Theorem 1. It extends the guarantee of the dynamic learning algorithm to choices among several options, as in the LP relaxation of the AdWords problem, at the price of $\log k$ in the size condition.
--
--   **Formalization Note** The proof in the paper refers to that of Theorem 1, which aims at the constants $10$ and $15$; the union bound there does not support these values, and Theorem 3 prints none, so the constants are existential and quantified first. The expectation is the average over all $n!$ arrival orders. The logarithm is natural. For $\varepsilon=2^{-E}$, $E\ge1$, with $\varepsilon n$ a positive integer, the algorithm is exactly that of §3 with the rule of §5.1.
--
--   Differences from the source:
--   - reading: "1 − O(ε) competitive" and "B ≥ Ω(m log(nk/ε)/ε²)" → there exist C₁, C₂ > 0, chosen before m, n, k, ε, the data and both selection rules; reason: this is the uniform meaning of the asymptotic notation
--   - reading: "for all inputs", under endnote 4 ("at most m arrivals such that there are ties"), read with Appendix D.1 → inputs in general position, a tie being a nonunique maximum among the zero score of rejection and the k surpluses; reason: this is the technical assumption of §5.1. It excludes degenerate inputs, on which the unperturbed rule can fail (identical arrivals f = g = 1 with a binding capacity are all rejected at price 1); the paper handles them by random perturbation
--   - reading: "for any ε > 0", with an algorithm and analysis written for ε = 2^(−E) and εn an integer, without loss of generality → every real ε > 0 and every horizon, with δ = 2^(−E) for E = max(1, ⌈log₂(1/ε)⌉), learning times ⌈2^r δn⌉, and a best-reward proposal when δn < 1; reason: the paper leaves the rounding implicit; on its dyadic, integral regime the algorithm is unchanged and no case is excluded
--   - reading: a right-hand side b, constrained only through the lower bound on B → b ≥ 0 is assumed in addition to that lower bound; reason: the bound is nonpositive when log(nk/ε) ≤ 0, and since g ≥ 0 a negative b_i makes problem (3) infeasible and OPT undefined; only infeasible inputs are excluded
--   - reading: n vectors in ℝ^k and m constraints, with B = min_i b_i → m ≥ 1, n ≥ 1 and k ≥ 1; reason: the dimensions are implicitly positive, as the minimum and the logarithm require; only empty problems are excluded
--   - encoding: "the optimal dual solution" and "we break ties arbitrarily" → the bound holds for every prefix-only selection of an optimal dual price and every prefix-only tie-breaking rule; reason: optimal prices and maximizers need not be unique
--   - encoding: expectation over a uniformly random permutation of the blocks, and an unspecified base of the logarithm → the finite average over all permutations, and the natural logarithm; reason: the expectations are equal, and the base is absorbed by C₁
--   - generalization: Appendix D.1's list of tie equations: two equal option surpluses f_tj − p^T g_tj = f_tl − p^T g_tl, or an option surplus equal to 0, at any level → only arrivals whose largest score among rejection (0) and the k surpluses is attained twice are counted; reason: a tie below the largest score changes neither the optimal block decision of (D1) nor the allocation rule; every such counted arrival satisfies one of D.1's equations, so every input in the source's general position satisfies this hypothesis, and the statement covers more inputs
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 878, Theorem 3 (proof: p. 886, §5.1, and p. 889, Appendix D; endnote 4)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_DynamicOnlineLP_DLA_Algorithm
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SimplexPackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SurplusRule
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_GeneralPosition
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_MultiInstance
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_MultiAlgorithm

namespace DynamicOnlineLP.DLA.Supplement

/-- Theorem 3 (Agrawal–Wang–Ye 2014, p. 878), with absolute constants `C₁, C₂` in place of the
paper's `Ω(·)` and `O(·)`: for every `ε > 0`, every input of the general online LP (3) in general
position with `b ≥ 0` and `min_i b_i ≥ C₁ m log(nk/ε)/ε²`, and every valid selection of dual
prices and of ties, the multidimensional DLA satisfies
`E_σ[∑_t f_tᵀ x_t] ≥ (1 - C₂ ε) OPT`. -/
theorem multidim_dla_competitive_ratio :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (m n k : ℕ) (ε : ℝ) (I : MultiInstance m n k) (rule : MultiDualRule m n k)
        (tie : TieRule m n k),
        1 ≤ m → 1 ≤ n → 1 ≤ k → 0 < ε →
        I.GeneralPosition → IsValidMultiDualRule rule → IsValidTieRule tie →
        (∀ i : Fin m, 0 ≤ I.b i) →
        (∀ i : Fin m, C₁ * (m : ℝ) * Real.log ((n : ℝ) * (k : ℝ) / ε) / ε ^ 2 ≤ I.b i) →
        (1 - C₂ * ε) * I.OPT ≤
          avgPerm (fun σ : Equiv.Perm (Fin n) => multiValue I rule tie ε σ) := by sorry

end DynamicOnlineLP.DLA.Supplement
