-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_cylEnd_shift
-- name    : FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_cylEnd_shift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T21:35:17.641529+00:00
-- url     : https://prove2.me/theorems/5834c7b0-4c69-46c5-8c63-482ee62934e8
-- title:
--   Shifted cylindrical coordinates of an end converge in $C^\infty_{loc}$ to a trivial cylinder
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$, Reeb field $R$ and a $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb{R}\times S\cong\mathbb{R}^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. Let $P=(x,T)$ be a periodic Reeb orbit (degenerate orbits allowed) and $\sigma\in\{1,-1\}$. Write $a(s,t)$, $w(s,t)$ for the components of $u(e^{-2\pi(s+it)})$ in the cylindrical coordinates at the puncture.
--
--   Assume that for every $\varepsilon>0$ there is $r_0>0$ such that for each $0<r<r_0$ some phase $c'$ satisfies
--   $$\sup_{t}\big\|w\big(r e^{-2\pi i t}\big)-x(\sigma T t+c')\big\|\le\varepsilon .$$
--   Then for every sequence $s_j\to\infty$ there are a subsequence (not relabelled) and a phase $c\in\mathbb{R}$ such that
--   $$a(s+s_j,t)-a(s_j,0)\longrightarrow \sigma T s,\qquad w(s+s_j,t)\longrightarrow x(\sigma T t+c)$$
--   in $C^\infty_{loc}(\mathbb{R}^2)$, i.e. with all derivatives, uniformly on compact subsets of $\mathbb{R}^2$.
--
--   This is the compactness statement behind the $C^\infty$ convergence, up to phase, of the end $(a,w)$ to the trivial cylinder over $P$.
--
--   **Formalization Note** `endA H u cylEnd` and `endW H u cylEnd` are $a$ and $w$ in the coordinates `cylEnd s t` $=e^{-2\pi(s+it)}$; the shifted maps are `p ↦ endA H u cylEnd (p + (s_j, 0)) - endA H u cylEnd (s_j, 0)` and `p ↦ endW H u cylEnd (p + (s_j, 0))` on `ℝ × ℝ`. $C^\infty_{loc}$ convergence is `JHolomorphic.TendstoCInftyLocOn` on `Set.univ`; the subsequence is a strictly monotone `φ`. The loop hypothesis uses `loopInS H u (cwLoop 0 r)`, eventually in `𝓝[>] 0`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, Lemma 2.4 and its proof

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a finite-energy `J̃`-holomorphic curve on `D \ {0}`, `P = (x, T)` a periodic Reeb
orbit and `σ = ±1`. Suppose that for every `ε > 0`, every clockwise loop
`t ↦ proj(u(r e^{-2π i t}))` of sufficiently small radius `r > 0` is uniformly `ε`-close to some
reparametrization `t ↦ x(σ T t + c')`. Then for every sequence `s_j → ∞` there are a subsequence
and a phase `c` such that, in the cylindrical coordinates `cylEnd` at `0`, the shifted maps
`(s, t) ↦ a(s + s_j, t) - a(s_j, 0)` converge in `C^∞_loc(ℝ²)` to `(s, t) ↦ σ T s`, and the shifted
maps `(s, t) ↦ w(s + s_j, t)` converge in `C^∞_loc(ℝ²)` to `(s, t) ↦ x(σ T t + c)`. -/
theorem exists_subseq_tendstoCInftyLocOn_cylEnd_shift {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hloop : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ t : ℝ,
      ‖loopInS H u (cwLoop 0 r) t - P.x (σ * P.T * t + c')‖ ≤ ε)
    (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c : ℝ,
      JHolomorphic.TendstoCInftyLocOn
        (fun j (p : ℝ × ℝ) => endA H u cylEnd (p + (s (φ j), 0)) - endA H u cylEnd (s (φ j), 0))
        (fun p => σ * P.T * p.1) Set.univ ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j (p : ℝ × ℝ) => endW H u cylEnd (p + (s (φ j), 0)))
        (fun p => P.x (σ * P.T * p.2 + c)) Set.univ := by
  sorry

end FiniteEnergyPlane
