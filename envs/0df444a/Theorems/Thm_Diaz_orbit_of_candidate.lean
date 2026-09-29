-- Prove2me | Theorems.Thm_Diaz_orbit_of_candidate
-- name    : Diaz.orbit_of_candidate
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:17:45.048016+00:00
-- url     : https://prove2.me/theorems/a31668ce-3926-4c2f-aea0-efbf00b2c133
-- title:
--   The four-point orbit of a candidate on its circle
-- statement:
--   Let $u \neq 0$ with $e^{u}$ and $u\bar u$ algebraic. Then each of
--
--   $$u,\quad -u,\quad \bar u,\quad -\bar u$$
--
--   is again such a point and has the same squared modulus $u\bar u$, and the four are pairwise distinct.
--
--   **Where this sits.** This is the orbit clause of a same-circle independence statement of Carlo Perassi's: "The four points are distinct because $u$ is off the axes, and all lie in $\mathcal{D} \cap C_r$: the set $\mathcal{D}$ is stable under negation and conjugation, and both preserve the modulus."
--
--   **Proof.** $e^{-u} = (e^{u})^{-1}$ and $e^{\bar u} = \overline{e^{u}}$ are algebraic, the first because the inverse of a non-zero algebraic number is algebraic, the second because complex conjugation is a $\mathbb{Q}$-algebra map of $\mathbb{C}$. The moduli agree by a one-line computation. Distinctness reduces to $u \neq 0$ together with $\bar u \neq u$ and $\bar u \neq -u$; those two are Hermite–Lindemann, since $\bar u = \pm u$ makes $u^{2} = \pm u\bar u$ algebraic and hence $u$ algebraic, while $u \neq 0$ has algebraic exponential.
--
--   **What is deliberately not claimed.** The substance of that statement — that two candidates on one centered algebraic circle are algebraically independent unless they lie in a common orbit, and that $\mathcal{D} \cap C_r \cap \overline{\mathbb{Q}(u)}$ is exactly this orbit — descends from his pair dichotomy and through it from Theorem 0.2 of Roy–Waldschmidt. That input is not available in Mathlib and nothing of it is asserted here. The same substance also follows from Theorem 6.7 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.10, 27 September 2026, GitHub release note-v1.10), on this mission as the Proved node `DiazModulus.log_pair_rigid_of_trdeg_one`, since for two candidates $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(u,\bar u,v,\bar v) = \operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(u,v)$. This node records only that the orbit exists, is genuinely of size four, and stays inside the locus.
--
--   Novelty is not asserted.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.orbit_of_candidate {u : ℂ} (hu0 : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) (hρ : IsAlgebraic ℚ (u * conj u)) :
    (∀ v ∈ ({u, -u, conj u, -conj u} : Set ℂ),
        v ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp v) ∧ v * conj v = u * conj u)
      ∧ u ≠ -u ∧ u ≠ conj u ∧ u ≠ -conj u
      ∧ -u ≠ conj u ∧ -u ≠ -conj u ∧ conj u ≠ -conj u := by sorry
