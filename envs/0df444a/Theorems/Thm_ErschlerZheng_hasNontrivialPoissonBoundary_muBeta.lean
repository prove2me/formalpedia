-- Prove2me | Theorems.Thm_ErschlerZheng_hasNontrivialPoissonBoundary_muBeta
-- name    : ErschlerZheng.hasNontrivialPoissonBoundary_muBeta
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T09:05:10.005416+00:00
-- url     : https://prove2.me/theorems/bffc6be4-9614-4283-8287-a8827bc77ec1
-- title:
--   Theorem 7.13 — for β ∈ (1 − 1/D, 1) and an integer A > D(1+β)/(2(1−β)) divisible by D, μ_β with k_n = A⌊log₂ n⌋ has non-trivial Poisson boundary
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $1 - \frac1D < \beta < 1$, and let $A$ be an integer divisible by $D$ with $A > \frac{D(1+\beta)}{2(1-\beta)}$. Then the measure $\mu_\beta$ on $G_\omega$ (`muBeta`) of (7.11) with $k_n = A\lfloor\log_2 n\rfloor$ (`kLog A`) has non-trivial Poisson boundary (`HasNontrivialPoissonBoundary`).
--
--   Erschler and Zheng, p. 43, Theorem 7.13: “Let $\omega$ be a string satisfying Assumption $(\mathrm{Fr}(D))$. Then for $\beta \in (1 - \frac1D, 1)$ and integer $A > \frac{D(1+\beta)}{2(1-\beta)}$ divisible by $D$, the measure $\mu_\beta$ on $G_\omega$ defined as in (7.11) with $k_n = A\lfloor\log_2 n\rfloor$ has non-trivial Poisson boundary.”
--
--   `HasNontrivialPoissonBoundary` asks for a bounded $\mu_\beta$-harmonic function that is not constant on the set of products of elements of the support of $\mu_\beta$. $A$ is a natural number.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 43, Theorem 7.13

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem hasNontrivialPoissonBoundary_muBeta (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (β : ℝ) (hβ1 : 1 - 1 / (D : ℝ) < β) (hβ2 : β < 1) (A : ℕ)
    (hA : (D : ℝ) * (1 + β) / (2 * (1 - β)) < A) (hDA : D ∣ A) :
    HasNontrivialPoissonBoundary (muBeta D ω (kLog A) β) := by
  sorry

end ErschlerZheng
