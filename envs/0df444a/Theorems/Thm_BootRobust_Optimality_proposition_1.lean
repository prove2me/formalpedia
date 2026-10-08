-- Prove2me | Theorems.Thm_BootRobust_Optimality_proposition_1
-- name    : BootRobust.Optimality.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:53.595983+00:00
-- url     : https://prove2.me/theorems/331fe2da-8527-47a9-8c4e-f612aec3f96a
-- title:
--   Proposition 1, p. 16 — a distance R > B(·, D_tr) near some D with B(D, D_tr) = r admits a nominal formulation with bootstrap disappointment rate > −r
-- statement:
--   Let $R$ be a distribution distance function on $\mathcal D_n$ (Definition 4). Let $D,D_{\rm tr}\in\mathcal D_n$, with $D_{\rm tr}$ of full support, and $B(D,D_{\rm tr})=r$. Suppose that $R(D',D_{\rm tr})>r$ for all $D'$ in some neighbourhood $\mathcal N\subseteq\mathcal D_n$ of $D$, open in $\mathcal D_n$. Then there is a nominal formulation — a nonnegative loss $G:\iota\to\mathbb R_+$ with cost estimator $D\mapsto\mathbb E_D[G]=\sum_iD_iG_i$ — whose disappointment set under the robust counterpart (24) with distance $R$ and radius $r$,
--   $$\mathcal R=\Big\{D\in\mathcal D_n:\ \mathbb E_D[G]>\sup_{D'\in\mathcal D_n,\ R(D',D_{\rm tr})\le r}\mathbb E_{D'}[G]\Big\},$$
--   satisfies
--   $$-r<\liminf_{n\to\infty}\frac1n\log D^\infty_{\rm tr}\big[D_{{\rm bs}[n]}\in\mathcal R\big].$$
--   Equivalently: there is $\varepsilon>0$ such that, for all sufficiently large $n$,
--   $$D_{\rm tr}^n\big[D_{{\rm bs}[n]}\in\mathcal R\big]\ge\exp\big(-n(r-\varepsilon)\big).$$
--
--   Theorem 6 shows that with the bootstrap distance $B$ the disappointment decays at rate at least $r$. Proposition 1 says that $B$ is the smallest distance function with this guarantee: any distance function that exceeds $B$ on an open set around some $D$ loses the rate $-r$ for some nominal formulation.
--
--   **Formalization Note** The statement is in the equivalent explicit-$\varepsilon$ form, which avoids $\log 0$ and an extended-real limit inferior. The support $\Omega_n$ is a finite type and only support points enter; with $w\equiv1$ and $k(n)=n$ the estimator (18) of a loss $G$ is $\mathbb E_D[G]$, so the decision $z^r_{\rm tr}(x_0)$ plays no role. $G\ge 0$ makes the loss admissible under Assumption 1. The neighbourhood is open relative to $\mathcal D_n$, and $D_{\rm tr}>0$ is the paper's convention that $\Omega_n$ is the support of the training data.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, Proposition 1, p. 16; proof in B.2, p. 27

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting

namespace BootRobust.Optimality

open MeasureTheory

/-- Proposition 1, p. 16. Let `R` be a distribution distance function, `D, D_tr ∈ 𝒟ₙ` with
`B(D, D_tr) = r`, and `N ⊆ 𝒟ₙ` a relatively open neighbourhood of `D` on which `R(·, D_tr) > r`.
Then there is a nominal formulation (cost estimator `D ↦ 𝔼_D[G]` with a nonnegative loss `G`) whose
disappointment set `ℛ` under the robust counterpart (24) with distance `R` satisfies
`-r < liminf (1/n) log D^∞_tr[D_bs[n] ∈ ℛ]`, stated equivalently as: for some `ε > 0`, eventually
`Dⁿ_tr(D_bs[n] ∈ ℛ) ≥ exp(-n (r - ε))`. -/
theorem proposition_1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (R : (ι → ℝ) → (ι → ℝ) → EReal) (hR : IsDistributionDistance R)
    (D Dtr : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) (hB : BootRobust.Perf.bootDist D Dtr = (r : EReal))
    (N : Set (ι → ℝ)) (hN : relOpen N) (hDN : D ∈ N)
    (hRN : ∀ D' ∈ N, (r : EReal) < R D' Dtr) :
    ∃ G : ι → ℝ, (∀ i, 0 ≤ G i) ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (Real.exp (-((n : ℝ) * (r - ε)))) ≤
        bootLaw Dtr n {ω | empDist ω ∈ linDisapp R Dtr r G} := by sorry

end BootRobust.Optimality
