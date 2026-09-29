-- Prove2me | Theorems.Thm_Diaz_normal_form
-- name    : Diaz.normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T06:59:32.608586+00:00
-- url     : https://prove2.me/theorems/72e875b7-76ef-4bce-a2d1-17b4bde2556e
-- title:
--   The elementary normal form: algebraic modulus, algebraic norm, and the affine conic $XY=\rho$
-- statement:
--   **Source.** A definition of the Diaz candidate locus together with the display that
--   follows it, unpublished apart from this node. The mathematics is Carlo Perassi's. Nothing here is claimed as
--   new; the content is elementary.
--
--   **Statement.** Let $u \in \mathbb{C}$ with $u \neq 0$. Then
--
--   1. $|u|$ is algebraic over $\mathbb{Q}$ if and only if $u\bar u$ is;
--   2. $u\bar u$ is algebraic over $\mathbb{Q}$ if and only if there is a real number $\rho$ with
--      $\rho > 0$, $\rho$ algebraic over $\mathbb{Q}$, and $u\bar u = \rho$.
--
--   In Lean the first `IsAlgebraic ℚ` is read in $\mathbb{R}$ (`‖u‖ : ℝ`), the second in $\mathbb{C}$
--   (`u * conj u : ℂ`), and the $\rho$ of part 2 is real with its coercion to $\mathbb{C}$ appearing
--   in the equation. Part of the content of part 1 is exactly that this change of ambient field does
--   not matter.
--
--   **Why this is the normal form.** Write
--   $\mathcal{L} = \{u \in \mathbb{C} : e^{u} \in \overline{\mathbb{Q}}^{\times}\}$ for the logarithms
--   of non-zero algebraic numbers and
--   $$\mathcal{D} = \{u \in \mathcal{L}\setminus\{0\} : u\bar u \in \overline{\mathbb{Q}}\}$$
--   for the locus of hypothetical counterexamples to Diaz's conjecture, which asserts $\mathcal{D} =
--   \varnothing$. Part 1 is the assertion, made in the definition cited above, that $\mathcal{D}$ is equally well
--   described by "$|u|$ algebraic" — the two descriptions of the locus agree. Part 2 carries that
--   description over to the geometric one: a candidate is precisely a logarithmic point
--   $(u, \bar u) \in \mathcal{L}^{2}$ on the **affine** conic
--   $$X_{\rho} := \{(X,Y) \in \mathbb{C}^{2} : XY = \rho\}, \qquad
--   \rho \in \overline{\mathbb{Q}} \cap \mathbb{R}_{>0}.$$
--   That conic is the one on which Section 4 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9) places a candidate, and its affineness — as against
--   a homogeneous quadric — is where the available rank criteria for points of $\mathcal{L}^{n}$ on
--   quadrics stop applying.
--
--   **Scope.** Neither part mentions the exponential: both are statements about one non-zero complex
--   number, and the hypothesis $u \neq 0$ enters only to make $\rho$ strictly positive. This node
--   therefore reduces nothing about Diaz's conjecture; it fixes the coordinates the rest of the
--   argument works in.
--
--   The proof is the identity $u\bar u = |u|^{2}$, the fact that a complex number is algebraic exactly
--   when its square is, and the fact that the inclusion $\mathbb{R} \hookrightarrow \mathbb{C}$ both
--   preserves and reflects algebraicity over $\mathbb{Q}$.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.normal_form {u : ℂ} (hu : u ≠ 0) :
    (IsAlgebraic ℚ ‖u‖ ↔ IsAlgebraic ℚ (u * conj u)) ∧
      (IsAlgebraic ℚ (u * conj u) ↔
        ∃ ρ : ℝ, 0 < ρ ∧ IsAlgebraic ℚ ρ ∧ u * conj u = (ρ : ℂ)) := by sorry
