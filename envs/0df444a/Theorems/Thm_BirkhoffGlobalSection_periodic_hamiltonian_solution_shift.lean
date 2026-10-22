-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_periodic_hamiltonian_solution_shift
-- name    : BirkhoffGlobalSection.periodic_hamiltonian_solution_shift
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-01T21:05:35.065882+00:00
-- url     : https://prove2.me/theorems/b879a18d-9873-4f0b-8635-5fb8a501b060
-- title:
--   Shift-invariance of anchored-periodic Hamiltonian solutions
-- statement:
--   Let $x : \mathbb{R} \to \mathbb{R}^4$ be a trajectory of the autonomous Levi--Civita Hamiltonian vector field that stays on the selected left energy component and closes up after time $T$:
--
--   $$x(T) = x(0).$$
--
--   Then $x$ repeats with period $T$ from every starting time:
--
--   $$x(s + T) = x(s) \qquad (s \in \mathbb{R}).$$
--
--   Here $\mu$ and $c$ are the mass ratio and energy parameters. Both $t \mapsto x(t)$ and $t \mapsto x(t + T)$ solve the same autonomous equation with the same value at $t = 0$, so uniqueness of solutions gives the identity; the component stays away from the second collision, where the field is smooth, so uniqueness applies along the trajectory.
--
--   This is the ODE-infrastructure lemma that turns anchored periodicity (closing up after $T$ from time $0$) into a return after every visit, which is what the no-short-return estimate needs. It is reusable wherever anchored-periodic Hamiltonian solutions appear.
--
--   **Formalization Note** No positivity of $T$ is assumed. The component hypothesis keeps the trajectory inside the locus where the vector field is smooth.
-- source:
--   Standard autonomous-ODE fact: uniqueness of solutions implies shift-invariance of anchored-periodic solutions (Picard--Lindelof); e.g. Teschl, Ordinary Differential Equations and Dynamical Systems, Chapter 2. Specialized here to the Levi--Civita field on its regular component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Shift-invariance of anchored-periodic Hamiltonian solutions: a trajectory
of the autonomous Levi--Civita field staying on the selected component and
closing up after time `T` repeats with period `T` from every starting time.
Both `t ↦ x t` and `t ↦ x (t + T)` solve the same autonomous equation with
the same value at `t = 0`, so uniqueness of solutions gives the identity.
The component stays away from the second collision, where the field is
smooth, so uniqueness applies along the trajectory. -/
theorem periodic_hamiltonian_solution_shift
    (μ c : ℝ) (x : ℝ → Phase) (T : ℝ)
    (hmem : ∀ t : ℝ, x t ∈ leftEnergyComponent μ c)
    (hsol : ∀ t : ℝ, HasDerivAt x
      (hamiltonianVectorField (leviCivitaHamiltonian μ c) (x t)) t)
    (hper : x T = x 0) :
    ∀ s : ℝ, x (s + T) = x s := by sorry

end BirkhoffGlobalSection
