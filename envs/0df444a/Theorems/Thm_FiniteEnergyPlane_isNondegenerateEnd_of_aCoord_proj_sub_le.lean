-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_of_aCoord_proj_sub_le
-- name    : FiniteEnergyPlane.isNondegenerateEnd_of_aCoord_proj_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T18:37:48.268855+00:00
-- url     : https://prove2.me/theorems/e3a5ed28-80b0-4667-9047-fdfc1b7206d4
-- title:
--   A nondegenerate end is stable under polynomially small perturbations of the symplectization coordinates
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$, let $P=(x,T)$ be a periodic Reeb orbit on $S$, and write $a(y)$ and $\mathrm{proj}(y)\in S$ for the symplectization coordinates of $y\ne0$ ($y=e^{2a}\,\mathrm{proj}(y)$). Let $u:\mathbb C\to\mathbb R^{2n+2}$ be asymptotic to $P$ at $\infty$ in the sense of Hryniewicz, Definition 2.9 (1), (2), (4): in the coordinates $z=e^{2\pi(s+it)}$ there are $d,c$ and $b>0$ with $a(u)-Ts-d\to0$ and $e^{bs}\big(\mathrm{proj}(u)-x(Tt+c)\big)\to0$ uniformly in $t$ as $s\to+\infty$.
--
--   Let $f:\mathbb C\to\mathbb R^{2n+2}$ and suppose there are $R$, $K$ and $\kappa>0$ such that for all $|z|\ge R$
--   $$|a(f(z))-a(u(z))|\le K(1+|z|)^{-\kappa},\qquad \|\mathrm{proj}(f(z))-\mathrm{proj}(u(z))\|\le K(1+|z|)^{-\kappa}.$$
--   Then $f$ is asymptotic to $P$ at $\infty$ in the same sense.
--
--   The statement lets one transfer the asymptotic behaviour of a known plane to maps that are only known to be close to it at a polynomial rate in $|z|$.
--
--   Formalization Note: the end is `IsNondegenerateEnd H u cylInf P 1`, with `cylInf s t` $=e^{2\pi(s+it)}$. No regularity or equation is assumed on $f$, and $H$ is an arbitrary function; the constants $d$, $c$ of $f$ are not asserted to be related to those of $u$ in the conclusion.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Definition 2.9

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A nondegenerate end is stable under polynomially small perturbations of the symplectization
coordinates. Let `u : ℂ → V n` be asymptotic to the periodic Reeb orbit `P` at `∞` in the sense of
`IsNondegenerateEnd`, and let `f : ℂ → V n` satisfy, for some `κ > 0` and all `‖z‖ ≥ R`,
`|aCoord (f z) - aCoord (u z)| ≤ K (1 + ‖z‖)^{-κ}` and
`‖proj (f z) - proj (u z)‖ ≤ K (1 + ‖z‖)^{-κ}`. Then `f` is asymptotic to `P` at `∞` in the same
sense. -/
theorem isNondegenerateEnd_of_aCoord_proj_sub_le {n : ℕ} (H : V n → ℝ) (P : ReebOrbit H)
    (u f : ℂ → V n) (huP : IsNondegenerateEnd H u cylInf P 1) (R K κ : ℝ) (hκ : 0 < κ)
    (h : ∀ z, R ≤ ‖z‖ → |aCoord H (f z) - aCoord H (u z)| ≤ K * (1 + ‖z‖) ^ (-κ) ∧
      ‖proj H (f z) - proj H (u z)‖ ≤ K * (1 + ‖z‖) ^ (-κ)) :
    IsNondegenerateEnd H f cylInf P 1 := by
  sorry

end FiniteEnergyPlane
