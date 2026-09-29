-- Prove2me | Theorems.Thm_DSSYKScales_cosmic_hamiltonian_fluctuation_diverges
-- name    : DSSYKScales.cosmic_hamiltonian_fluctuation_diverges
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T02:03:36.763687+00:00
-- url     : https://prove2.me/theorems/9d0897c6-b9af-4161-bc65-cc4a20787f10
-- title:
--   $\langle H_c^2\rangle$ grows linearly in $N$ and diverges: $H_c\notin\mathcal A_c$
-- statement:
--   Let $(N_n,q_n)$ be double scaled with parameter $\lambda>0$, and let $\mathcal J\neq0$. Let $\langle H_c^2\rangle_{N,q}=\binom Nq\,\frac{q!}{N^{q-1}}\,\mathcal J^2$ be the infinite-temperature second moment of the cosmic Hamiltonian (3.4). Then
--   $$\lim_{n\to\infty}\frac{\langle H_c^2\rangle_{N_n,q_n}}{N_n}=\mathcal J^2e^{-\lambda/2}\qquad\text{and}\qquad \langle H_c^2\rangle_{N_n,q_n}\longrightarrow+\infty .$$
--
--   This is eq. (11.1), $\langle H_c^2\rangle=\mathcal J^2N$: the fluctuation of $H_c$ in the maximally mixed state grows linearly in $N$ and diverges. By the criterion of Witten and Chandrasekaran-Longo-Penington-Witten, the cosmic Hamiltonian is therefore not in the cosmic algebra $\mathcal A_c$.
--
--   **Formalization Note** The paper approximates $\binom Nq\approx N^q/q!$ (below (3.9)). In the double-scaled regime $q^2/N\to\lambda$ the exact count gives an extra factor: $\binom Nq q!/N^q\to e^{-\lambda/2}$. The limit is therefore $\mathcal J^2e^{-\lambda/2}$ rather than $\mathcal J^2$. The paper's qualitative conclusion (linear growth in $N$, divergence) is unchanged. The operator-level computation of $\langle H_c^2\rangle$ is encoded in the definition, not proved.
-- source:
--   L. Susskind, "De Sitter Space, Double-Scaled SYK, and the Separation of Scales in the Semiclassical Limit", arXiv:2209.09999v1 [hep-th] (2022), https://arxiv.org/abs/2209.09999, Section 11 (The Algebra of Observables), p. 47, eq. (11.1); also Section 3.1, eqs. (3.4), (3.9)-(3.10)

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem cosmic_hamiltonian_fluctuation_diverges (N q : ℕ → ℕ) (lam J : ℝ) (hJ : J ≠ 0)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => cosmicHamiltonianSecondMoment (N n) (q n) J / (N n : ℝ))
      atTop (𝓝 (J ^ 2 * Real.exp (-(lam / 2)))) ∧
    Tendsto (fun n => cosmicHamiltonianSecondMoment (N n) (q n) J) atTop atTop := by sorry
end DSSYKScales
