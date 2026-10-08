-- Prove2me | Theorems.Thm_ErschlerZheng_hasNontrivialPoissonBoundary_of_tsum_green_mul_mass_lt_top
-- name    : ErschlerZheng.hasNontrivialPoissonBoundary_of_tsum_green_mul_mass_lt_top
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T00:00:39.078373+00:00
-- url     : https://prove2.me/theorems/b4932cea-b96b-4635-9833-4c084200949a
-- title:
--   Proposition 3.3 — if the Green-weighted mass (3.2) of germs outside ℋ(H_o) is finite, the Poisson boundary of (G, μ) is non-trivial
-- statement:
--   Let a group $H$ act from the right on a topological space $X$, each map $y \mapsto y \cdot h$ continuous. Let $G \le H$ be countable and $L \le H$ an auxiliary group with trivial isotropy for $G$ (`IsAuxiliary`). Let $o \in X$ be a point with $\hat{\mathcal G}_o$ (= `isotropy (G ⊔ L) o`) non-trivial and $\hat{\mathcal G}_o = \mathcal G_o$ (= `isotropy G o`). Let $\mu$ be a non-degenerate probability on $G$ (`IsProbability`, `IsNondegenerate`), and $H_o$ a proper subgroup of $\hat{\mathcal G}_o$. Suppose
--   $$\sum_{x \in o \cdot G} \mathbf G_{P_\mu}(o, x)\, \mu(\{g \in G : (g, x) \notin \mathcal H\}) < \infty,$$
--   where $\mathcal H = \mathcal H(H_o)$ is `germSubgroupoid G L o Ho`, $P_\mu$ is the induced transition kernel on the orbit $o \cdot G$ (`orbitKernel G μ o`), and $\mathbf G_{P_\mu}(o, x) = \sum_{n \ge 0} P_\mu^n(o, x) \in [0, \infty]$ is its Green function (`MarkovChain.green`). Then the Poisson boundary of $(G, \mu)$ is non-trivial (`HasNontrivialPoissonBoundary μ`).
--
--   Erschler and Zheng, pp. 18–19, Proposition 3.3: “Let $G$ be a countable group acting by homeomorphisms on $\mathcal X$ from the right and $L$ be an auxiliary group with trivial isotropy. Assume that the isotropy group $\hat{\mathcal G}_o$ is nontrivial at some point $o \in \mathcal X$ and $\hat{\mathcal G}_o = \mathcal G_o$. Let $\mu$ be a non-degenerate probability measure on $G$. Let $P_\mu$ be the induced transition kernel on the orbit $o \cdot G$ and $\mathbf G_{P_\mu}$ the Green function of the $P_\mu$-random walk. Suppose there exists a proper subgroup $H_o \lneqq \hat{\mathcal G}_o$ such that (3.2) $\sum_{x \in o \cdot G} \mathbf G_{P_\mu}(o, x)\mu(\{g \in G : (g, x) \notin \mathcal H\}) < \infty$, where $\mathcal H = \mathcal H(H_0)$ is the sub-groupoid of $\mathcal G$ associated with $H_o$ defined in (3.1). Then the Poisson boundary of $(G, \mu)$ is non-trivial.”
--
--   ($H_0$ is $H_o$.) The Green function is that of p. 18, “$\mathbf G_{P_\mu}(x, y) = \sum_{n=0}^\infty P_\mu^n(x, y)$”. The sum (3.2) is taken in $[0, \infty]$, so a point with infinite Green function is allowed only if no element of the support of $\mu$ has a germ outside $\mathcal H$ there. The base point enters the Green function as an element `o₀` of the orbit with `o₀ = o`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), pp. 18–19, Proposition 3.3

import Mathlib
import Definitions.Def_ErschlerZheng_Germs
import Definitions.Def_MarkovChain_HeatKernels
open scoped RightActions

namespace ErschlerZheng

theorem hasNontrivialPoissonBoundary_of_tsum_green_mul_mass_lt_top {H : Type*} [Group H]
    {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X]
    [DecidableEq X] (G L : Subgroup H) [Countable G] (hL : IsAuxiliary (X := X) G L) (o : X)
    (hGo : isotropy (G ⊔ L) o ≠ ⊥) (hGGo : isotropy (G ⊔ L) o = isotropy G o)
    (μ : G → ℝ) (hμ : IsProbability μ) (hnd : IsNondegenerate μ)
    (o₀ : rightOrbit G o) (ho₀ : (o₀ : X) = o)
    (Ho : Subgroup (GermGroup (H := H) o)) (hHo : Ho < isotropy (G ⊔ L) o)
    (hsum : ∑' x : rightOrbit G o, MarkovChain.green (orbitKernel G μ o) o₀ x *
        ENNReal.ofReal (mass μ {g : G | ((g : H), (x : X)) ∉ germSubgroupoid G L o Ho}) < ⊤) :
    HasNontrivialPoissonBoundary μ := by
  sorry

end ErschlerZheng
