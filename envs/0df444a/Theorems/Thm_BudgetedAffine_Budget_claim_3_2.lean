-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_claim_3_2
-- name    : BudgetedAffine.Budget.claim_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:27:15.476965+00:00
-- url     : https://prove2.me/theorems/04afcfde-0e6a-412b-a9e3-18603acdbc75
-- title:
--   Claim 3.2 — the rounding (2Z_i/η) is feasible for (3.7) with probability ≥ 1 − n·e^δ/(1+δ)^{1+δ}, δ = η/2 − 2
-- statement:
--   Let $n\ge3$, $B\in\mathbb R^{m\times n}_+$, $d\in\mathbb R^n_+$, $\mathcal J\subseteq[m]$, $\gamma>0$ and $w_i\in(0,1]$ for $i\in\mathcal J$, and assume condition 1 of Lemma 3.3:
--   $$z(e_i)>4\gamma\cdot\frac{\log n}{\log\log n}\cdot w_i\qquad\text{for all } i\in\mathcal J.$$
--   Let $\eta=4\log n/\log\log n$, let $\hat d,\hat B$ be the rescaled data of Section 3.3, and let $z^*$ be a feasible solution of the packing problem (3.7). Let $\xi_i\sim\mathrm{Ber}(z^*_i-\lfloor z^*_i\rfloor)$ be independent and $Z_i=\lfloor z^*_i\rfloor+\xi_i$. With $\delta=\eta/2-2$,
--   $$\mathbb P\Big(\big(\tfrac{2Z_i}{\eta}\big)_{i\in\mathcal J}\text{ is feasible for (3.7)}\Big)\ \ge\ 1-n\cdot\frac{e^\delta}{(1+\delta)^{1+\delta}}.$$
--
--   This is the high-probability dual feasibility of the randomized rounding in the proof of Lemma 3.3; the right-hand side tends to $1$ as $n\to\infty$.
--
--   **Formalization Note** The paper states "with probability at least $1-O(1/n)$". Its proof (App. A, p. 31) applies Lemma B.1 with $s=\hat d_j\ge1$ and a union bound over the $n$ columns, which gives exactly the bound above; the subsequent step to $O(1/n)$ is not valid (the exponent $\tfrac\eta2\log\tfrac\eta2\,\hat d_j$ is smaller than $2\hat d_j\log n$ for large $n$), and the bound above is $n^{-1+o(1)}$-close to $1$, not $O(1/n)$. The explicit bound is what the proof of Lemma 3.3 needs. The paper takes $z^*$ optimal for (3.7); only feasibility is used, and only feasibility is assumed. Probabilities are those of independent Bernoulli selection from $\mathcal J$ (the referenced definition `SpectralSparsify.Sampling.BernoulliSubset`): the outcome is the set $T\subseteq\mathcal J$ of indices with $\xi_i=1$, and $Z_i=\lfloor z^*_i\rfloor+\mathbb 1[i\in T]$. $n\ge3$ makes $\delta>0$.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Claim 3.2, p. 13 (proof App. A, pp. 31–32)

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_BudgetedAffine_Budget_Rescaling
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset

namespace BudgetedAffine.Budget

open Matrix SpectralSparsify.Sampling

/-- Claim 3.2 (in the explicit form its proof establishes): in the setting of Lemma 3.3 with
condition 1, `η = 4 log n / log log n` and `δ = η/2 − 2`, for a feasible solution `z*` of the
packing problem (3.7) and the randomized rounding `Zᵢ = ⌊z*ᵢ⌋ + ξᵢ` (`i ∈ J`) with independent
`ξᵢ ~ Ber(z*ᵢ − ⌊z*ᵢ⌋)` (the outcome is the set `T ⊆ J` of indices with `ξᵢ = 1`), the vector
`(2Zᵢ/η)_{i ∈ J}` is feasible for (3.7) with probability at least `1 − n · e^δ / (1 + δ)^{1+δ}`. -/
theorem claim_3_2 {m n : ℕ} (hn : 3 ≤ n) (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (J : Finset (Fin m)) (γ : ℝ) (w : Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hd : 0 ≤ d) (hγ : 0 < γ) (hw : ∀ i ∈ J, 0 < w i ∧ w i ≤ 1)
    (hcond1 : ∀ i ∈ J,
      ((4 * γ * (Real.log n / Real.log (Real.log n)) * w i : ℝ) : EReal) <
        coverCost B d (Pi.single i 1))
    (zs : Fin m → ℝ) (hzs : DualFeasible (BHat B w J) (dHat B d w J (beta n) γ) J zs) :
    1 - n * (Real.exp (beta n / 2 - 2) / (1 + (beta n / 2 - 2)) ^ (1 + (beta n / 2 - 2))) ≤
      prob J (fun i => zs i - ⌊zs i⌋)
        (fun T => DualFeasible (BHat B w J) (dHat B d w J (beta n) γ) J
          (fun i => 2 * ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0) / beta n)) := by sorry

end BudgetedAffine.Budget
