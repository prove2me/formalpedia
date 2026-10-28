-- Prove2me | Theorems.Thm_FiniteEnergyPlane_punctured_disk_asymptotics
-- name    : FiniteEnergyPlane.punctured_disk_asymptotics
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T23:26:27.954304+00:00
-- url     : https://prove2.me/theorems/4aca064f-c3c0-4736-9a5b-21c05f6c61dd
-- title:
--   Asymptotics of finite-energy punctured disks in the symplectization of a star-shaped level
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $D\subset\mathbb{C}$ the open unit disc, and $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$. Then either the puncture $0$ is removable, or there is $Q\neq0$ such that the actions of the clockwise loops $t\mapsto u(\rho e^{-2\pi it})$ converge to $Q$ as $\rho\to0^+$, and:
--   1. if $Q>0$ then $a(u(z))\to+\infty$ as $z\to0$; if $Q<0$ then $a(u(z))\to-\infty$ as $z\to0$;
--   2. for every sequence $\rho_k\to0^+$ there are a subsequence $\rho_{k_j}$, a periodic Reeb orbit $P=(x,|Q|)$ and $c\in\mathbb{R}$ with
--   $$\mathrm{proj}\,u\big(\rho_{k_j}e^{-2\pi i\,\cdot}\big)\longrightarrow x(Q\,\cdot+c)\quad\text{in }C^\infty(\mathbb{R},V).$$
--
--   **Formalization Note** Removability is `IsRemovablePuncture H J u 0 1` (a smooth $\tilde J$-holomorphic extension to $D$ that avoids $0$). The charge is the limit of `loopAction H u (cwLoop 0 ρ)` along `𝓝[>] 0`. One loop orientation (clockwise around $0$, Wendl's $\phi_+$) applies to both signs, so at a negative puncture the limit $x(Qt+c)$ with $Q<0$ runs the orbit backward; Wendl parametrizes negative ends by $\phi_-$. Wendl's statement that $a$ is asymptotic to $\pm|Q|s$ plus a constant, and the convergence for all $s$ when the orbit is nondegenerate or Morse–Bott, are not part of this item.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Theorem 9.8, p. 157 (without the nondegenerate and Morse–Bott clause); H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Wendl, Theorem 9.8 (p. 157), without the nondegenerate and Morse–Bott clause; Hofer 1993,
§ 3. Let `u` be a finite-energy `J̃`-holomorphic curve on the punctured unit disc. Either the
puncture is removable, or the actions `Q(ρ)` of the clockwise loops `t ↦ u(ρ e^{-2π i t})` converge
as `ρ → 0⁺` to a charge `Q ≠ 0`. In the second case `a(u(z)) → +∞` as `z → 0` if `Q > 0`
(positive puncture) and `a(u(z)) → -∞` if `Q < 0` (negative puncture). Moreover, for every
`ρ_k → 0⁺` a subsequence of the loops `t ↦ proj(u(ρ_k e^{-2π i t}))` converges in `C^∞` to
`t ↦ x(Q t + c)` for a periodic Reeb orbit `(x, |Q|)`. (One loop orientation, clockwise around
`0` as for Wendl's positive ends `ϕ₊`, is used for both signs, so at a negative puncture the
limit `x(Q t + c)` with `Q < 0` runs the orbit backward; Wendl parametrizes negative ends by `ϕ₋`.) -/
theorem punctured_disk_asymptotics {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    IsRemovablePuncture H J u 0 1 ∨
      ∃ Q : ℝ, Q ≠ 0 ∧ Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 Q) ∧
        (0 < Q → Tendsto (fun z => aCoord H (u z)) (𝓝[≠] 0) atTop) ∧
        (Q < 0 → Tendsto (fun z => aCoord H (u z)) (𝓝[≠] 0) atBot) ∧
        ∀ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) → Tendsto ρ atTop (𝓝 0) →
          ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H, P.T = |Q| ∧ ∃ c : ℝ,
            TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ (φ k))))
              (fun t => P.x (Q * t + c)) := by
  sorry

end FiniteEnergyPlane
