-- Prove2me | Theorems.Thm_Erdos142_r_add_le
-- name    : Erdos142.r_add_le
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:37:53.431608+00:00
-- url     : https://prove2.me/theorems/8d6e9949-619b-4dcf-abf7-bed634a2c84a
-- title:
--   Subadditivity: $r_k(M+N) \le r_k(M) + r_k(N)$
-- statement:
--   For all $k$, $M$ and $N$,
--
--   $$r_k(M+N) \;\le\; r_k(M) + r_k(N).$$
--
--   Given a $k$-AP-free set $A \subseteq \{1,\dots,M+N\}$, split it into the part lying in $\{1,\dots,M\}$ and the part lying in $\{M+1,\dots,M+N\}$. Both parts are again $k$-AP-free, being subsets of a $k$-AP-free set, and the second becomes a $k$-AP-free subset of $\{1,\dots,N\}$ after translation by $M$, since translating a set neither creates nor destroys arithmetic progressions. Adding the two bounds gives the inequality.
--
--   Subadditivity is the structural backbone of the subject: it is what makes the density $r_k(N)/N$ converge (Fekete's lemma), so that Szemerédi's theorem can be stated as the assertion that the limit is zero, and it is what allows a bound proved on a subinterval to be assembled into a bound on the whole range. Mathlib records the $k=3$ case as `rothNumberNat_add_le`.
-- source:
--   Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27]); the general-$k$ analogue of Mathlib's `rothNumberNat_add_le` (Mathlib/Combinatorics/Additive/AP/Three/Defs.lean).

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem r_add_le (k M N : ℕ) : r k (M + N) ≤ r k M + r k N := by sorry

end Erdos142
