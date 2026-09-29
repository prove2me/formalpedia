-- Prove2me | Theorems.Thm_DFT_potential_diff_const_of_eigenfunction
-- name    : DFT.potential_diff_const_of_eigenfunction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:03:29.863033+00:00
-- url     : https://prove2.me/theorems/b33a3e88-96bf-40c8-92f7-dd3a26fafea4
-- title:
--   Hohenberg-Kohn Theorem 1 (the potential is determined up to a constant)
-- statement:
--   This is the potential half of Hohenberg-Kohn Theorem 1: "if two systems of electrons, one
--   trapped in a potential $v_1$ and the other in $v_2$, have the same ground-state density, then
--   $v_1 - v_2$ is necessarily a constant".
--
--   Suppose $N = n+1$ electrons move in $\mathbb R^3$ and that a single wavefunction $\Psi$ on
--   $(\mathbb R^3)^{N}$ is a ground state of the two Hamiltonians built from external potentials
--   $v_1$ and $v_2$. Subtracting the two eigenvalue equations leaves the algebraic relation
--
--   $$\Bigl(\sum_{i=1}^{N} w(r_i)\Bigr)\,\Psi(r_1,\dots,r_N) \;=\; c\,\Psi(r_1,\dots,r_N),
--   \qquad w := v_1 - v_2,\quad c := E_1 - E_2 .$$
--
--   The theorem states the conclusion drawn from that relation: if $w$ is measurable and $\Psi$ is
--   nonzero almost everywhere on configuration space, and the displayed relation holds almost
--   everywhere, then
--
--   $$w(r) \;=\; \frac{c}{N} \quad \text{for almost every } r \in \mathbb R^3 ,$$
--
--   so the two external potentials differ by a constant, and the constant is the energy difference
--   divided by the electron number.
--
--   The hypothesis that $\Psi$ does not vanish on a set of positive measure is where unique
--   continuation for Schrodinger operators enters the physical argument; here it is an explicit
--   hypothesis, so the statement is a clean measure-theoretic lemma independent of any operator
--   theory.
--
--   **Formalization Note.** Almost-everywhere statements are with respect to Lebesgue measure on
--   $(\mathbb R^3)^{N}$ and on $\mathbb R^3$ respectively. The electron number is written $n+1$
--   so that it is positive, which is needed for the division by $N$.
-- source:
--   Wikipedia, 'Density functional theory' (uploaded PDF), sections 'Derivation and formalism', 'Hohenberg-Kohn theorems' (Theorem 1, Corollary 1, Theorem 2) and 'Kohn-Sham equations'; https://en.wikipedia.org/wiki/Density_functional_theory . Primary sources cited there: P. Hohenberg and W. Kohn, 'Inhomogeneous electron gas', Phys. Rev. 136 (1964) B864, https://doi.org/10.1103/PhysRev.136.B864 ; W. Kohn and L. J. Sham, Phys. Rev. 140 (1965) A1133, https://doi.org/10.1103/PhysRev.140.A1133 ; M. Levy, Proc. Natl. Acad. Sci. USA 76 (1979) 6062, https://doi.org/10.1073/pnas.76.12.6062 .

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory

namespace DFT

theorem potential_diff_const_of_eigenfunction {n : ℕ} (w : Pos → ℝ) (hw : Measurable w)
    (c : ℝ) (Ψ : Config n → ℂ) (hΨ : ∀ᵐ x, Ψ x ≠ 0)
    (heq : ∀ᵐ x, (∑ i, w (x i)) • Ψ x = c • Ψ x) :
    ∀ᵐ r, w r = c / (n + 1) := by sorry

end DFT
