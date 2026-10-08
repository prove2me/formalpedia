-- Prove2me | Theorems.Thm_CosmoConstCentury_einstein_static_universe_unstable
-- name    : CosmoConstCentury.einstein_static_universe_unstable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-05T02:34:24.80609+00:00
-- url     : https://prove2.me/theorems/5ccb8b51-a1c1-4bba-92f4-ffdfe40f7f45
-- title:
--   Eddington: Einstein's static universe is unstable
-- statement:
--   Let $G>0$, $c>0$, and let $R_0>0$, $\rho_0$ be such that the constant pair $(R_0,\rho_0)$ is a static solution of the closed ($k=1$) Friedmann–Lemaître dust equations (15)–(16) with cosmological constant $\Lambda$ (Einstein's static universe). Then this solution is unstable: there is $\delta>0$ such that for every $\varepsilon>0$ there exist a time $T>0$ and a solution $(R,\rho)$ of the same equations, with the same $\Lambda$, on the time interval $[0,T]$, such that
--   $$|R(0)-R_0|<\varepsilon,\qquad |R'(0)|<\varepsilon,\qquad |\rho(0)-\rho_0|<\varepsilon,$$
--   but
--   $$|R(T)-R_0|\ge\delta .$$
--
--   This is the instability described in Section 3.1 (Eddington 1930): an arbitrarily small perturbation of the Einstein world drives it away from the static state, into contraction or runaway expansion.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 3.1, pp. 80-81 (Eddington 1930, 1933); static solution eq. (10) p. 78; equations (15)-(16) p. 82.

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem einstein_static_universe_unstable (G c Λ R₀ ρ₀ : ℝ) (hG : 0 < G) (hc : 0 < c)
    (hR₀ : 0 < R₀)
    (hstatic : IsFriedmannSolution G c Λ 1 Set.univ (fun _ => R₀) (fun _ => ρ₀)) :
    ∃ δ > 0, ∀ ε > 0, ∃ (R ρ : ℝ → ℝ) (T : ℝ), 0 < T ∧
      IsFriedmannSolution G c Λ 1 (Set.Icc 0 T) R ρ ∧
      |R 0 - R₀| < ε ∧ |deriv R 0| < ε ∧ |ρ 0 - ρ₀| < ε ∧ δ ≤ |R T - R₀| := by sorry

end CosmoConstCentury
