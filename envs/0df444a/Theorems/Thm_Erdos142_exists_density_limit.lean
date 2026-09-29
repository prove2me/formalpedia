-- Prove2me | Theorems.Thm_Erdos142_exists_density_limit
-- name    : Erdos142.exists_density_limit
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:38:45.716298+00:00
-- url     : https://prove2.me/theorems/8a617cde-68a8-4c93-a5ee-44cd969e6893
-- title:
--   The density $r_k(N)/N$ converges
-- statement:
--   For every $k \ge 1$ there is a real number $c$ with
--
--   $$\lim_{N\to\infty}\frac{r_k(N)}{N} \;=\; c .$$
--
--   The sequence $N \mapsto r_k(N)$ is subadditive and non-negative, so Fekete's subadditivity lemma applies and the ratios $r_k(N)/N$ converge to their infimum, which lies in $[0,1]$.
--
--   The existence of this limit is what turns Szemerédi's theorem into a sharp statement rather than a vague one: the *upper* density of a progression-free set is automatically well defined, and Szemerédi's theorem is exactly the assertion that the limit $c$ equals $0$ for every $k \ge 3$. Proving convergence first, without identifying the value, isolates the soft part of the story from the hard part and gives later milestones a stable object to work with.
-- source:
--   Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27]); Fekete's subadditivity lemma applied to $r_k$, as noted in the docstring of Mathlib's `rothNumberNat_add_le`.

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem exists_density_limit (k : ℕ) (hk : 0 < k) :
    ∃ c : ℝ, Filter.Tendsto (fun N : ℕ => (r k N : ℝ) / (N : ℝ)) Filter.atTop (nhds c) := by sorry

end Erdos142
