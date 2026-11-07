-- Prove2me | Theorems.Thm_CFLOutliers_appendixB_operation_count
-- name    : CFLOutliers.appendixB_operation_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:08.313133+00:00
-- url     : https://prove2.me/theorems/7db9d34c-d9e2-4bfa-8f7e-073969b8e46b
-- title:
--   Appendix B — the accepted-operation count $N\tau\le nK\eta$
-- statement:
--   Let the instance satisfy the standing assumptions, let $\eta>0$, $\tau>0$ and $K\in\mathbb N$, let $S_0$ be the empty solution, and for $k=1,\dots,K$ let $S_k$ be the output of a run of $\mathrm{Local}(k\eta,\tau;S_{k-1})$ with $N_k$ accepted changes. Then the total number $N=\sum_{k=1}^K N_k$ of accepted operations satisfies
--
--   $$N\tau\le nK\eta .$$
--
--   With the parameters (21), $\tau=\varepsilon B/(100m)$ and $\eta=\varepsilon B/(100n)$, this gives $N\le nK\eta/\tau=mK=O(mn/\varepsilon)$, the bound that makes the algorithm polynomial in the input length and $1/\varepsilon$.
--
--   Differences from the source:
--   - generalization: a finite metric space with distances c → a pseudometric on the index set F ⊔ C (distinct points may be at distance 0); reason: it covers every metric instance, including a facility co-located with a client; no step of the paper uses positivity of distances
--   - generalization: τ, η of (21) and K = ⌈400n/ε⌉ → any η > 0, τ > 0 and K; reason: the telescoping argument of p.15 uses only that raising the penalty by η costs at most nη, that each accepted change decreases Φ by more than τ, and that Φ starts at 0 and stays nonnegative
--   - generalization: the runs of the algorithm → every run of Local at each grid point; reason: the paper's runs are among them
--   - encoding: "Nτ ≤ nKη, N ≤ nKη/τ = mK = O(mn/ε)" → Nτ ≤ nKη; reason: equivalent to N ≤ nKη/τ for τ > 0; nKη/τ = mK is arithmetic under (21)
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Appendix B, "Running time", p.15

import Mathlib
import Definitions.Def_CFLOutliers_LocalRun

namespace CFLOutliers

open Finset

/-- **The accepted-operation count** (Dabas, arXiv:2611.04094, Appendix B, "Running time", p.15).
For an instance satisfying the standing assumptions, a grid step `η > 0`, a threshold `τ > 0` and
`K` grid points, let `S₀` be the empty solution and `S_k` the output of a run of
`Local(kη, τ; S_{k−1})` with `N_k` accepted changes, `k = 1, …, K`. Then the total number
`N = Σ_k N_k` of accepted operations satisfies `N τ ≤ n K η`.

**Formalization Note.** Stated for every `η, τ, K` and every run; with (21)
(`τ = εB/(100m)`, `η = εB/(100n)`) it gives `N ≤ nKη/τ = mK`. -/
theorem appendixB_operation_count (I : Inst) (hI : I.Std) (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ)
    (K : ℕ) (S : ℕ → Sol I) (N : ℕ → ℕ) (h0 : S 0 = Sol.empty I)
    (hrun : ∀ k, 1 ≤ k → k ≤ K → LocalRun ((k : ℝ) * η) τ (S (k - 1)) (S k) (N k)) :
    ((∑ k ∈ Icc 1 K, N k : ℕ) : ℝ) * τ ≤ (I.n : ℝ) * K * η := by sorry

end CFLOutliers
