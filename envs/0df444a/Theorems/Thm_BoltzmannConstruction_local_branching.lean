-- Prove2me | Theorems.Thm_BoltzmannConstruction_local_branching
-- name    : BoltzmannConstruction.local_branching
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-07T18:37:27.972242+00:00
-- url     : https://prove2.me/theorems/f86bfe3e-d214-4660-ab94-825a193b1b1f
-- title:
--   Separated finite-interval entropy solutions from bounded-velocity data
-- statement:
--   For the periodic hard-sphere Boltzmann equation on the unit three-torus, there exist an initial density $f_0$ supported in a bounded velocity ball, a time $T>0$, and two finite-interval entropy-admissible evolutions $F,G$ with that same datum. Both evolutions are strongly continuous in $L^1$ on $[0,T]$, with separately integrable unrenormalized collision gain and loss. There are an interior time $0<t<T$ and a measurable observable $\psi$ on phase space, with $|\psi|\le1$, such that
--
--   $$\int F(t,z)\psi(z)\,dz
--   e\int G(t,z)\psi(z)\,dz.$$
--
--   Finite-interval admissibility includes the renormalized and local-mass identities with terminal traces, the every-time momentum identity, and the energy and entropy-dissipation inequalities. This is the local construction and separation part of Theorem 1.1, separated from the global continuation problem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/build/sections/10-separation.tex; Section 10, proof of Theorem 1.1, before global continuation; Section 6, Proposition 6.1 (admissible limits). The bounded observable is the L¹ dual separation of the distinct time sections.

import Definitions.Def_BoltzmannFiniteInterval

noncomputable section
open MeasureTheory Set Filter
open OAI.BoltzmannNonuniqueness

namespace BoltzmannConstruction

/-- The cold-jet/cap construction produces separated finite-interval solutions.
The bounded observable records separation without choosing representatives. -/
theorem local_branching :
    ∃ f₀ : Density, BoundedVelocitySupport f₀ ∧
      ∃ (F G : Evolution) (T : ℝ), AdmissibleOn f₀ T F ∧ AdmissibleOn f₀ T G ∧
        StrongEarly T F ∧ StrongEarly T G ∧
        ∃ (t : ℝ) (ψ : Phase → ℝ), t ∈ Set.Ioo 0 T ∧ Measurable ψ ∧
          (∀ z, |ψ z| ≤ 1) ∧
          (∫ z, F t z * ψ z) ≠ (∫ z, G t z * ψ z) := by sorry

end BoltzmannConstruction
