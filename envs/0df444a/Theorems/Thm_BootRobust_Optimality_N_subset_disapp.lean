-- Prove2me | Theorems.Thm_BootRobust_Optimality_N_subset_disapp
-- name    : BootRobust.Optimality.N_subset_disapp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:24.143314+00:00
-- url     : https://prove2.me/theorems/e0234481-40f8-4115-be7f-0f1d29af611e
-- title:
--   B.2, p. 27 — int 𝒩 = 𝒩 ⊆ ℛ′ ⊆ ℛ for the separating functional
-- statement:
--   Let $R:\mathcal D_n\times\mathcal D_n\to(-\infty,+\infty]$, $D_{\rm tr}$, $r\in\mathbb R$, a loss $G:\iota\to\mathbb R$ and $a\in\mathbb R$ be given, and let $\mathcal N\subseteq\mathcal D_n$ be open in $\mathcal D_n$. Suppose
--   $$\mathbb E_D[G]\le a\ \text{ whenever } D\in\mathcal D_n,\ R(D,D_{\rm tr})\le r,\qquad a<\mathbb E_{D'}[G]\ \text{ for all } D'\in\mathcal N.$$
--   Then ${\rm int}\,\mathcal N=\mathcal N$ (interior relative to $\mathcal D_n$) and
--   $$\mathcal N\subseteq\mathcal R=\Big\{D\in\mathcal D_n:\ \mathbb E_D[G]>\sup_{D'\in\mathcal D_n,\ R(D',D_{\rm tr})\le r}\mathbb E_{D'}[G]\Big\},$$
--   the disappointment set of the nominal formulation with cost estimator $D\mapsto\mathbb E_D[G]$.
--
--   This places the separating neighbourhood inside the disappointment set, so a lower bound on the bootstrap probability of $\mathcal N$ is one for $\mathcal R$.
--
--   **Formalization Note** The supremum is taken in the extended reals.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.2 (proof of Proposition 1), p. 27, "Hence, int N = N ⊆ R′ …"

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting

namespace BootRobust.Optimality

/-- B.2, p. 27: if `𝔼_D[G] ≤ a < 𝔼_{D'}[G]` for every `D` in the `R`-ball of radius `r` around `D_tr`
and every `D'` in a relatively open set `N`, then `int N = N` (interior relative to `𝒟ₙ`) and `N` lies
in the disappointment set `ℛ` of the nominal formulation with cost estimator `D ↦ 𝔼_D[G]`. -/
theorem N_subset_disapp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : (ι → ℝ) → (ι → ℝ) → EReal) (Dtr : ι → ℝ) (r : ℝ)
    (N : Set (ι → ℝ)) (hN : relOpen N) (G : ι → ℝ) (a : ℝ)
    (hball : ∀ D ∈ stdSimplex ℝ ι, R D Dtr ≤ (r : EReal) → ∑ i, D i * G i ≤ a)
    (hNsep : ∀ D' ∈ N, a < ∑ i, D' i * G i) :
    relInt N = N ∧ N ⊆ linDisapp R Dtr r G := by sorry

end BootRobust.Optimality
