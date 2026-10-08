-- Prove2me | Theorems.Thm_BSUMConv_BSCA_eq_34
-- name    : BSUMConv.BSCA.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:50.916999+00:00
-- url     : https://prove2.me/theorems/d40d3954-fee5-493d-9d76-8c1bc79fe880
-- title:
--   (34), p. 18 — a further subsequence has vanishing directions
-- statement:
--   Under the hypotheses of Theorem 4, take a convergent subsequence $x^{r_q}\to z$ whose selected block is the same block $k$ at every listed step. There is a further subsequence of these indices for which
--   $$d^{r_q}=y^{r_q}-x^{r_q}\longrightarrow0.$$
--
--   The vanishing direction allows the block minimum relation to pass to the limit.
--
--   **Formalization Note** The paper chooses the first block without loss of generality; the statement uses an arbitrary fixed block. The subsequence and further subsequence are represented by strictly increasing maps on natural numbers.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 18, (34)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSCA_Setting

namespace BSUMConv.BSCA

open Filter Topology TsengBCD.Stationary

/-- Display (34), p. 18: along a convergent subsequence updating one block, a further
subsequence has vanishing search directions. -/
theorem eq_34 {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (f : X n → ℝ)
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (s : ℕ → Fin N) (σ β αinit : ℝ) (x y : ℕ → X n) (j : ℕ → ℕ)
    (hclosed : ∀ i, IsClosed (Xs i)) (hconvXs : ∀ i, Convex ℝ (Xs i))
    (hC1 : ContDiff ℝ 1 f) (hmatch : FirstOrderAgreement Xs f h)
    (hstrict : StrictApprox Xs h) (hcont : ContinuousApprox Xs h)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 < αinit) (hα1 : αinit ≤ 1)
    (hcyclic : IsCyclic s) (hrun : IsBSCARun Xs f h s σ β αinit x y j)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (z : X n)
    (hz : Tendsto (fun q => x (φ q)) atTop (𝓝 z))
    (k : Fin N) (hk : ∀ q, s (φ q) = k) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun q => y (φ (ψ q)) - x (φ (ψ q))) atTop (𝓝 0) := by sorry

end BSUMConv.BSCA
