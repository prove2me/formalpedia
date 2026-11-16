-- Prove2me | Theorems.Thm_BordenaveCollins_tendsto_expFix
-- name    : BordenaveCollins.tendsto_expFix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:09:41.669317+00:00
-- url     : https://prove2.me/theorems/d1374481-30d3-415e-834d-17c595a19241
-- title:
--   First-order asymptotics of the expected number of fixed points of a word in random permutations and perfect matchings
-- statement:
--   Let $g \ne e$ in $F_r * \Gamma_s$. With $\sigma_1, \dots, \sigma_r$ independent uniform permutations and $M_1, \dots, M_s$ independent uniform perfect matchings of $N$ points,
--   $$\mathbf E\big[\#\mathrm{fix}\, g(\sigma, M)\big] \longrightarrow c(g) + 1 \qquad\text{as } N \to \infty,$$
--   along all $N$ if $s = 0$ and along even $N$ otherwise. Here $c(g)$ (`cfun`) is the number of triples $(k, z, a)$ with $k \ge 2$, $z \ne e$, $g = a z^k a^{-1}$ and $\mathrm{len}(g) = 2\,\mathrm{len}(a) + k\,\mathrm{len}(z)$, minus $1$ if $g^2 = e$.
--
--   This is the counterpart, for permutations and perfect matchings together, of Lemma 5.2 of Chen, Garza-Vargas, Tropp and van Handel, *A new approach to strong convergence* (Nica's theorem for random permutations, where the limit is the number of divisors of the exponent of $g$ as a power of a non-power).
--
--   **Formalization note.** The definitions are in the bundle `Def_BordenaveCollins`. The limit is taken along $N = \mathrm{stp}(s)\, n$, $n \to \infty$, with $\mathrm{stp}(s) = 1$ if $s = 0$ and $2$ otherwise.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 20, Lemma 5.2, adapted to permutations and perfect matchings; a step of our proof of the theorem of Bordenave, C. and Collins, B., Eigenvalues of random lifts and polynomials of random permutation matrices, Ann. of Math. (2) 190 (2019) 811–875, https://doi.org/10.4007/annals.2019.190.3.3

import Mathlib
import Definitions.Def_BordenaveCollins

open Filter Topology

namespace BordenaveCollins

theorem tendsto_expFix {r s : ℕ} (g : G r s) (hg : g ≠ 1) :
    Tendsto (fun n : ℕ => expFix r s (stp s * n) g) atTop (𝓝 ((cfun g : ℝ) + 1)) := by
  sorry

end BordenaveCollins
