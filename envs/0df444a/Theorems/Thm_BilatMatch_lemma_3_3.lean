-- Prove2me | Theorems.Thm_BilatMatch_lemma_3_3
-- name    : BilatMatch.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:18.308013+00:00
-- url     : https://prove2.me/theorems/6884d4e9-8bc5-4e74-97ec-01981fa963b1
-- title:
--   Lemma 3.3 (Minimum Cost for a Given Trade Mass) — cutoff allocations minimize seller cost; $C_\alpha$ continuous and convex
-- statement:
--   Fix $\alpha\ge0$ and an $\alpha$-weakly regular seller prior $F_S$, either finitely supported or regular with interval support. Then:
--
--   1. for every $\mu\in[0,1]$, the cutoff allocation $Z_S(\mu,\cdot)$ is an allocation of mass $\mu$ with finite seller-side Lagrangian cost, and it minimizes $\mathbb E_{c\sim F_S}[\tau^\alpha_S(c)z(c)]$ among all allocations $z$ of mass $\mu$;
--   2. the cutoff allocations are nested in $\mu$;
--   3. $C_\alpha(\mu)=\mathbb E[\tau^\alpha_S(c)Z_S(\mu,c)]$ is continuous and convex on $[0,1]$;
--   4. for every initial cap $\kappa$ and $\mu\le F_S(\kappa)$, $Z_S(\mu,\cdot)$ is supported on $\kappa$, so the same minimum applies among allocations supported on $\kappa$.
--
--   **Formalization Note** An allocation is a measurable function $z:\mathbb R\to[0,1]$ and its mass is $\int z\,dF_S$.
--
--   Differences from the source:
--   - encoding: Cα is finite → τ^α_S · Z_S(µ,·) is integrable for every µ ∈ [0,1]; reason: the cost is a real number exactly when this integral exists
--   - encoding: for µ ≤ F_S(κ) the same minimum applies, with Z_S(µ,·) supported on κ → Z_S(µ,·) vanishes at every domain report outside κ for 0 ≤ µ ≤ F_S(κ); reason: with clause 1 this is the minimum among allocations supported on κ
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma 3.3, p.11 (pdf p.13); standing assumptions §3.2, p.10 (pdf p.12)

import Mathlib
import Definitions.Def_BilatMatch_sellerCost
import Definitions.Def_BilatMatch_typewise

open MeasureTheory

namespace BilatMatch

/-- **Lemma 3.3 (Minimum Cost for a Given Trade Mass).** Liu, Qin, Wang, arXiv:2609.30702 (held
version, sha256 ff1490ad…), Lemma 3.3, p.11 (pdf p.13); standing assumptions of §3.2, p.10.

Let `F_S` be `α`-weakly regular (`α ≥ 0`), with finite support or regular with interval support.
1. For every `µ ∈ [0, 1]` the cutoff allocation `Z_S(µ, ·)` is an allocation of mass `µ` with finite
   seller-side Lagrangian cost and minimizes `E[τ^α_S(c) z(c)]` among all allocations `z` of mass `µ`;
2. the cutoff allocations are nested in `µ`;
3. `C_α` is continuous and convex on `[0, 1]`;
4. for every initial cap `κ` and `µ ≤ F_S(κ)`, `Z_S(µ, ·)` is supported on `κ` (so the same minimum
   applies among allocations supported on `κ`).

**Formalization Note** An allocation (column) is a measurable `z : ℝ → [0, 1]`; its mass is
`∫ z dF_S`. "`C_α` is finite" is the integrability of `τ^α_S Z_S(µ, ·)`. -/
theorem lemma_3_3 (α : ℝ) (hα : 0 ≤ α) (F : Measure ℝ) (DS : Set ℝ) (τα : ℝ → ℝ)
    (hF : IsAlphaWeaklyRegular α F DS τα) :
    (∀ m ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun c => τα c * cutoffAlloc F m c) F ∧
      (∀ c ∈ DS, cutoffAlloc F m c ∈ Set.Icc (0 : ℝ) 1) ∧
      ∫ c, cutoffAlloc F m c ∂F = m ∧
      ∀ z : ℝ → ℝ, Measurable z → (∀ c, z c ∈ Set.Icc (0 : ℝ) 1) → ∫ c, z c ∂F = m →
        sellerCost F τα m ≤ ∫ c, τα c * z c ∂F) ∧
    (∀ m m' : ℝ, 0 ≤ m → m ≤ m' → m' ≤ 1 → ∀ c ∈ DS, cutoffAlloc F m c ≤ cutoffAlloc F m' c) ∧
    ContinuousOn (sellerCost F τα) (Set.Icc 0 1) ∧
    ConvexOn ℝ (Set.Icc 0 1) (sellerCost F τα) ∧
    (∀ κ : Set ℝ, IsCap DS κ → ∀ m ∈ Set.Icc (0 : ℝ) (F κ).toReal,
      ∀ c ∈ DS, c ∉ κ → cutoffAlloc F m c = 0) := by sorry

end BilatMatch
