-- Prove2me | Theorems.Thm_Diaz_normalization_not_invariant
-- name    : Diaz.normalization_not_invariant
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T06:59:43.918095+00:00
-- url     : https://prove2.me/theorems/d530f6f0-f34d-4809-9c15-c29389fddb97
-- title:
--   Normalizing to the unit circle is not an arithmetic invariance
-- statement:
--   **Source.** A remark of Carlo Perassi's, unpublished apart from this node: "Writing $u = rv$ with $|v| = 1$ changes the exponential condition to $e^{rv} \in
--   \overline{\mathbb{Q}}$; it does not imply $v \in \mathcal{L}$. Hence one cannot assume $\rho = 1$
--   without loss of arithmetic information." The mathematics is Carlo Perassi's; no novelty is claimed.
--   The witness below is the obvious one.
--
--   **Statement (conditional).** Assume Hermite–Lindemann in the form given as the hypothesis `HL`: for
--   every non-zero $z \in \mathbb{C}$ algebraic over $\mathbb{Q}$, $e^{z}$ is transcendental over
--   $\mathbb{Q}$. Then there exists $u \neq 0$ with $e^{u}$ algebraic — that is, $u \in \mathcal{L}$ —
--   such that $e^{u/|u|}$ is transcendental; so $u/|u| \notin \mathcal{L}$.
--
--   **Witness.** $u = 2\pi i$. Then $e^{u} = 1$ is algebraic, $|u| = 2\pi$, and $u/|u| = i$, whose
--   exponential is transcendental by `HL` applied to the non-zero algebraic number $i$.
--
--   **Reading.** The projection $u \mapsto u/|u|$ onto the unit circle destroys membership in
--   $\mathcal{L}$, which is the whole arithmetic content of the hypothesis. So the parameter $\rho =
--   u\bar u$ in the conic normal form $XY = \rho$ cannot be scaled away: the family of conics is not a
--   single conic in disguise, and a proof of Diaz's conjecture may not assume $\rho = 1$.
--
--   **On the hypothesis.** Hermite–Lindemann is a theorem (Hermite 1873, Lindemann 1882) but is not in
--   the platform's Mathlib at this revision — only the analytic half,
--   `NumberTheory.Transcendental.Lindemann.AnalyticalPart`, is present — so it is carried as an
--   explicit hypothesis, following the convention already used on this mission by
--   `DiazModulus.diaz_on_axes_of_hermite_lindemann`. It can be discharged against
--   `DiazModulus.hermite_lindemann_holds`. Only the instance at $z = i$ is used.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.normalization_not_invariant
    (HL : ∀ z : ℂ, z ≠ 0 → IsAlgebraic ℚ z → Transcendental ℚ (Complex.exp z)) :
    ∃ u : ℂ, u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp u) ∧
      Transcendental ℚ (Complex.exp ((((‖u‖ : ℝ) : ℂ))⁻¹ * u)) := by sorry
