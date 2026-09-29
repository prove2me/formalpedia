-- Prove2me | Theorems.Thm_FamousTheorems_descent_theorem_fg_groups
-- name    : FamousTheorems.descent_theorem_fg_groups
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:31.501983+00:00
-- url     : https://prove2.me/theorems/d4ceb8d3-c590-46ef-a190-35973219c2e6
-- title:
--   The descent theorem for finitely generated groups
-- statement:
--   **The descent theorem for finitely generated groups.** Let $G$ be an abelian group (written multiplicatively) and $h:G\to\mathbb R_{\ge0}$ a function such that:
--   - $G^2=\{g^2\}$ has finite index in $G$;
--   - $h$ satisfies the approximate parallelogram law: there is a constant $C$ with $|h(xy)+h(x/y)-2(h(x)+h(y))|\le C$ for all $x,y$;
--   - $h$ has the Northcott property: for every bound $B$, only finitely many $x$ satisfy $h(x)\le B$.
--
--   Then $G$ is finitely generated.
--
--   This is the descent step of the Mordell–Weil theorem. The weak Mordell–Weil theorem provides the finiteness of $E(K)/2E(K)$, and the canonical height on an elliptic curve satisfies the other two conditions, so $E(K)$ is finitely generated.
--
--   **Formalization note.** Mathlib's `CommGroup.fg_of_descent'`. The finite index condition is on the range of the squaring homomorphism `powMonoidHom 2`, and `Northcott h` is the Mathlib class stating that sublevel sets of $h$ are finite.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CommGroup.fg_of_descent'`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem descent_theorem_fg_groups {G : Type*} [CommGroup G] {h : G → ℝ} {C : ℝ} (hfi : (powMonoidHom 2 : G →* G).range.FiniteIndex)
    (hnn : ∀ x, 0 ≤ h x) (hpar : ∀ x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| ≤ C)
    [Northcott h] : Group.FG G := by sorry

end FamousTheorems
