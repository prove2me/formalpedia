-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_3_13
-- name    : ElimAgree.Supplement.theorem_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:37:03.136209+00:00
-- url     : https://prove2.me/theorems/3e366fd6-f6f9-4504-8af0-ec9501b176ba
-- title:
--   Theorem 3.13 (Graded local transfer) — cost $\ge[2\log(\gamma/\tau)-\log k+2\log g-2]_+$ under (3.5)
-- statement:
--   Assume hypothesis (3.5) for $f$ on $\Omega\times\Omega$ with parameters $\gamma,\tau>0$. Let $k\ge1$ and $0<g\le1$. Every public-coin protocol for $\mathrm{Elim}(f^k)$ with error at most $(1-g)2^{-k}$ on every input, with the output party designated at each leaf, has cost
--
--   $$c\ \ge\ \Big[2\log\frac\gamma\tau-\log k+2\log g-2\Big]_+ .$$
--
--   Here $\log$ is base two and $[x]_+=\max\{x,0\}$. Applied to disjointness through Lemma 3.14, this gives the $2\log n-\log k$ lower bound for local output (Corollary 3.15).
--
--   **Formalization Note** Both parties' inputs are $k$-tuples in $\Omega^k$; the leaf label and error are the base mission's designated-party convention.
--
--   Differences from the source:
--   - reading: k instances and error (1 − g)2^{−k} with 0 < g ≤ 1 (ranges implicit) → 1 ≤ k, 0 < g ≤ 1; reason: the paper's ranges; log k and log g are used
--   - encoding: a lower bound on R_ϵ (least worst-case cost) → every protocol of cost c (all trees in its support of depth ≤ c) with pointwise error ≤ ϵ has c ≥ the bound; reason: R is the least such cost, so the two say the same; avoids sInf of a possibly empty set
--   - encoding: L²(π) = ⊕ E_j orthogonally → a family of pairwise π-orthogonal subspaces of Ω → ℝ whose supremum is everything; reason: the same decomposition
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 3.13, p.13 (PDF p.15); hypothesis (3.5), p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_Models
import Definitions.Def_ElimAgree_Supplement_Hyp35

namespace ElimAgree

namespace Supplement

/-- Theorem 3.13 (Graded local transfer), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.13. Under
(3.5), every public-coin protocol for `Elim(f^k)` with error at most `(1 − g)2^{−k}`, with the
output party designated at each leaf, has cost `c ≥ [2 log(γ/τ) − log k + 2 log g − 2]_+`.

**Formalization Note.** `log` is `Real.logb 2` and `[x]_+ = max x 0`. Both parties' inputs are
`k`-tuples in `Ω^k`; error is pointwise; the leaf label is the base designated-party label and the
error is the base `desErr`. `0 < g ≤ 1` and `k ≥ 1` are the paper's ranges. -/
theorem theorem_3_13 {Ω : Type} [Fintype Ω] (π : Ω → ℝ) (f : Ω → Ω → Bool)
    (ν₁ ν₀ : Ω × Ω → ℝ) (γ τ : ℝ) (h35 : Hyp35 π f ν₁ ν₀ γ τ) (k : ℕ) (hk : 1 ≤ k) (g : ℝ)
    (hg : 0 < g) (hg1 : g ≤ 1) (c : ℕ) (μ : PMF (DesProt (Fin k → Ω) (Fin k → Ω) (Fin k → Bool)))
    (hc : CostLE μ c)
    (herr : ∀ x y, desErr (elimAns (X := fun _ => Ω) (Y := fun _ => Ω) (fun _ : Fin k => f)) μ x y ≤
      ENNReal.ofReal ((1 - g) / 2 ^ k)) :
    max (2 * Real.logb 2 (γ / τ) - Real.logb 2 k + 2 * Real.logb 2 g - 2) 0 ≤ (c : ℝ) := by sorry

end Supplement

end ElimAgree
