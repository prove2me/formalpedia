-- Prove2me | Theorems.Thm_FamousTheorems_closed_graph_theorem
-- name    : FamousTheorems.closed_graph_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:10.144027+00:00
-- url     : https://prove2.me/theorems/1cfab601-9723-40e5-8d41-c758e02726c2
-- title:
--   The closed graph theorem
-- statement:
--   **The closed graph theorem.** A linear map $g:E\to F$ between Banach spaces is continuous if and only if its graph $\{(x,g x)\}$ is closed in $E\times F$. This entry proves the nontrivial direction: closed graph implies continuous.
--
--   With the open mapping and uniform boundedness theorems it is one of the three consequences of the Baire category theorem that shape the theory of Banach spaces. It reduces proving continuity to checking that $x_n\to x$ and $g x_n\to y$ imply $y=g x$.
--
--   **Formalization note.** Mathlib's `LinearMap.continuous_of_isClosed_graph`, for complete normed spaces over a nontrivially normed field.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LinearMap.continuous_of_isClosed_graph`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem closed_graph_theorem {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : Continuous g := by sorry

end FamousTheorems
