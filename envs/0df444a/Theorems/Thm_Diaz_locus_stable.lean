-- Prove2me | Theorems.Thm_Diaz_locus_stable
-- name    : Diaz.locus_stable
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T06:59:34.41762+00:00
-- url     : https://prove2.me/theorems/086bbc65-2a83-483f-8565-e3f0eb57be68
-- title:
--   The candidate locus is stable under conjugation and under non-zero rational scaling
-- statement:
--   **Source.** The closing sentence of Carlo Perassi's definition of the candidate locus: "The set $\mathcal{D}$ is stable under $\mathbb{Q}^{\times}$, negation, and conjugation." The
--   mathematics is Carlo Perassi's and unpublished apart from this node; no novelty is claimed, and the statement is elementary.
--
--   **Statement.** Say that $u$ is a *candidate* when $u \neq 0$, $e^{u}$ is algebraic over
--   $\mathbb{Q}$ (that is, $u \in \mathcal{L}$), and $u\bar u$ is algebraic over $\mathbb{Q}$; Diaz's
--   conjecture is that no candidate exists. Then, for a candidate $u$:
--
--   * $\bar u$ is again a candidate;
--   * $q u$ is again a candidate, for every non-zero rational $q$.
--
--   Negation is the case $q = -1$, so the three stabilities of that sentence are covered by the two
--   clauses. The predicate is inlined into the statement rather than named, so the node depends on no
--   definition of its own.
--
--   **Proof.** For conjugation, $e^{\bar u} = \overline{e^{u}}$ and complex conjugation is a
--   $\mathbb{Q}$-algebra automorphism of $\mathbb{C}$, so it preserves algebraicity over $\mathbb{Q}$;
--   and $\bar u \, \overline{\bar u} = u \bar u$. For scaling, write $q = m/n$ with $m \in \mathbb{Z}$,
--   $n \in \mathbb{N}_{>0}$; then $\left(e^{qu}\right)^{n} = e^{mu} = \left(e^{u}\right)^{m}$, which is
--   algebraic, and a complex number with an algebraic power is algebraic. The modulus condition scales
--   as $(qu)\overline{(qu)} = q^{2}\, u \bar u$.
--
--   **What it is for.** It is the statement that lets one normalize a hypothetical counterexample
--   without loss: the locus is a union of punctured $\mathbb{Q}$-lines, closed under the reflection
--   that the whole problem is about. It reduces nothing — it says the set of counterexamples has these
--   symmetries, not that it is empty. Note that the *real*
--   scalings which would let one normalize $|u| = 1$ are exactly what this does **not** give:
--   $\mathbb{Q}^{\times}$ acts, $\mathbb{R}^{\times}$ does not.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.locus_stable {u : ℂ} (hu : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) (hmod : IsAlgebraic ℚ (u * conj u)) :
    (conj u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp (conj u)) ∧
        IsAlgebraic ℚ (conj u * conj (conj u))) ∧
      ∀ q : ℚ, q ≠ 0 →
        ((q : ℂ) * u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp ((q : ℂ) * u)) ∧
          IsAlgebraic ℚ (((q : ℂ) * u) * conj ((q : ℂ) * u))) := by sorry
