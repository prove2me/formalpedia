-- Prove2me | Theorems.Thm_Erdos142_erdos_142_variants_lower
-- name    : Erdos142.erdos_142_variants_lower
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:26:40.042154+00:00
-- url     : https://prove2.me/theorems/69f669e4-4854-4e52-b36a-667049c5b82b
-- title:
--   Erdős #142 (`variants.lower`): $r_k(N) = o_k(N/\log N)$
-- statement:
--   Let $r_k(N)$ be the largest possible size of a subset of $\{1,\dots,N\}$ that does not contain any non-trivial $k$-term arithmetic progression. The claim is that for every $k > 1$,
--
--   $$r_k(N) \;=\; o_k\!\left(\frac{N}{\log N}\right),$$
--
--   that is, $r_k(N)\log N / N \to 0$ as $N \to \infty$, with the rate allowed to depend on $k$.
--
--   This statement is `erdos_142.variants.lower` of the formal-conjectures entry for Erdős Problem #142, reproduced binder for binder over that file's own definition of $r_k$.
--
--   It is the one formalizable target in that file. The headline declaration there, `erdos_142`, asserts $r_k(N) = \Theta(f)$ with the comparison function left as a placeholder, and so do `variants.upper` and `variants.three`: the literal request of the problem — an asymptotic formula for $r_k(N)$ — has no known right-hand side for any $k \ge 3$. The displayed estimate is also the strongest precisely-stated form the problem page attaches to #142; Erdős offered 5000 dollars for (essentially) exactly it, which is the content of Erdős Problem #3. It is known for $k = 3$, where it follows from the bound of Bloom and Sisask and a fortiori from that of Kelley and Meka; it is trivial for $k = 2$, where $r_2(N) = 1$; and it is open for every $k \ge 4$. Proving it for all $k$ gives, by a standard summation argument, Erdős's conjecture that any set of natural numbers whose reciprocals sum to infinity contains arbitrarily long arithmetic progressions.
--
--   **Formalization Note.** The asymptotic relation is `Asymptotics.IsLittleO` along `Filter.atTop` on $\mathbb{N}$, applied to the real-valued casts. Real division is Lean's, so the comparison function is $0$ at $N = 1$; this is invisible to the `atTop` filter. The hypothesis is $1 < k$, exactly as in the source file.
-- source:
--   Google DeepMind, formal-conjectures, FormalConjectures/ErdosProblems/142.lean, theorem `erdos_142.variants.lower`, https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/142.lean ; Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27]); specifically the remark 'he elsewhere offered $5000 just for (essentially) showing that $r_k(N)=o_k(N/\log N)$ (see [3])'. See also Erdős Problem #3, https://www.erdosproblems.com/3.

import Mathlib
import Definitions.Def_Erdos142Basic
open Filter

namespace Erdos142

theorem erdos_142_variants_lower (k : ℕ) (hk : 1 < k) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by sorry

end Erdos142
