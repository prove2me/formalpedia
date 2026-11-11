-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_6
-- name    : BalancedFairAlloc.Existence.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:37:41.876541+00:00
-- url     : https://prove2.me/theorems/63144f9c-49dc-4bfb-9bae-dadefc598e17
-- title:
--   Lemma 6 — the label sets F_i are closed and cover the simplex
-- statement:
--   Assume $n\ge2$, $r\ge1$, $\rho\in(0,1/n)$, $\gamma>0$, $\varepsilon>0$, and let $w\mapsto p(w)\in\mathbb R^M$ be a price map continuous on $\Delta$. For each agent $i$ let
--
--   $$F_i=\Big\{w\in\Delta:\ \text{some }A\in R(\alpha(w),p(w),\varepsilon)\text{ has }d_i(A,w)=\min_kd_k(A,w)\Big\},$$
--
--   where $R(\alpha(w),p(w),\varepsilon)$ is the set of score maximizers and $d_k(A,w)$ the labels (22) with weights $\alpha(w)$. Then every $F_i$ is closed and $\bigcup_iF_i=\Delta$.
--
--   With $p=p^\lambda$ this is Lemma 6 for the sets $F_i^{\lambda,\varepsilon}$, the closed cover to which the KKM lemma is applied.
--
--   Differences from the source:
--   - generalization: prices p^λ(w), the regularized dual prices of (10), for a fixed λ > 0 → any price map continuous on Δ; reason: by Lemma 3 (with Lemma 23), p^λ is continuous on Δ, which is all the proof uses; λ no longer appears
--   - encoding: standing assumptions of Section 3 (p. 12: n ≥ 2 and r ≥ 1 without loss of generality) → explicit hypotheses `2 ≤ n` and `1 ≤ m / n`; reason: Lemmas 4-13 are stated in Section 3, under these assumptions
--   - encoding: ρ ∈ (0, 1/n) fixed on p. 13 → explicit hypotheses `0 < ρ` and `ρ < 1 / n`; reason: the weights α(w) of eq. (4) are defined under this choice
--   - encoding: γ > 0 and ε > 0 fixed in §3.3, §3.5 → explicit hypotheses; reason: the sets are defined under them
--   - encoding: closed subsets of Δ → closed in ℝ^n (`IsClosed`), each contained in Δ by definition; reason: Δ is closed in ℝ^n, so the two notions agree
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 20 (PDF 22), Lemma 6

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model
import Definitions.Def_BalancedFairAlloc_Existence_Score

namespace BalancedFairAlloc.Existence

theorem lemma_6 (n m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    (ρ γ ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / (n : ℝ)) (hγ : 0 < γ) (hε : 0 < ε)
    (pmap : (Fin n → ℝ) → Fin m → ℝ) (hp : ContinuousOn pmap (stdSimplex ℝ (Fin n))) :
    (∀ i, IsClosed (labelSet v ρ γ ε pmap i)) ∧
      (⋃ i, labelSet v ρ γ ε pmap i) = stdSimplex ℝ (Fin n) := by sorry

end BalancedFairAlloc.Existence
