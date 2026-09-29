-- Prove2me | Theorems.Thm_Erdos142_erdos_139_szemeredi
-- name    : Erdos142.erdos_139_szemeredi
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:40:03.014802+00:00
-- url     : https://prove2.me/theorems/7653083f-b258-4a2c-a86d-f689b72bf0ff
-- title:
--   Szemerédi's theorem (Erdős #139): $r_k(N) = o(N)$
-- statement:
--   For every $k > 1$,
--
--   $$\lim_{N \to \infty} \frac{r_k(N)}{N} \;=\; 0,$$
--
--   that is, $r_k(N) = o(N)$. Equivalently, every set of integers of positive upper density contains arbitrarily long arithmetic progressions.
--
--   This is Szemerédi's theorem, conjectured by Erdős and Turán in 1936, proved by Roth for $k = 3$ in 1953, by Szemerédi for $k = 4$ in 1969 and in general in 1975. It is the qualitative core of Erdős Problem #142: without it there is no asymptotic question to ask, and with it the entire remaining difficulty is quantitative. Furstenberg's 1977 ergodic-theoretic proof and Gowers's 2001 Fourier-analytic proof give two further routes, the latter with effective bounds.
--
--   The statement is `erdos_139` of the formal-conjectures repository, reproduced binder for binder over the same definition of $r_k$ that this mission's goal uses; erdosproblems.com/142 points at problem #139 under "see also". Combined with the milestone on the existence of $\lim_N r_k(N)/N$, it identifies that limit as $0$. No machine-checked proof of Szemerédi's theorem is known to exist in any proof assistant, for any $k \ge 3$; the $k = 3$ case (Roth's theorem) is also absent from Mathlib, although the surrounding infrastructure — the triangle removal lemma and Szemerédi's regularity lemma — is present.
--
--   **Formalization Note.** The limit is stated as convergence of the quotient to $0$, not as an `IsLittleO` relation; the two are equivalent along `atTop`. Real division is Lean's, so the quotient is $0$ at $N = 0$, which is invisible to the filter.
-- source:
--   Google DeepMind, formal-conjectures, FormalConjectures/ErdosProblems/139.lean, theorem `erdos_139`, https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/139.lean ; E. Szemeredi, On sets of integers containing no k elements in arithmetic progression, Acta Arith. 27 (1975), 199-245, https://doi.org/10.4064/aa-27-1-199-245; case k=3 due to K. F. Roth, On certain sets of integers, J. London Math. Soc. 28 (1953), 104-109. Conjectured by Erdos-Turan (1936). Erdos Problem #139, https://www.erdosproblems.com/139, linked from Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27])

import Mathlib
import Definitions.Def_Erdos142Basic
open scoped Topology

namespace Erdos142

theorem erdos_139_szemeredi (k : ℕ) (hk : 1 < k) :
    Filter.Tendsto (fun N => (r k N / N : ℝ)) Filter.atTop (𝓝 0) := by sorry

end Erdos142
