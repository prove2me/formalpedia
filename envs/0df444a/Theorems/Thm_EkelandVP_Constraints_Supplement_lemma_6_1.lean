-- Prove2me | Theorems.Thm_EkelandVP_Constraints_Supplement_lemma_6_1
-- name    : EkelandVP.Constraints.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:27:25.919344+00:00
-- url     : https://prove2.me/theorems/6e907004-5fdb-4de3-829f-153d7fad0358
-- title:
--   Lemma 6.1 — endpoint-preserving smooth density in the H¹ topology
-- statement:
--   Let $M$ be a connected complete strong smooth Riemannian Hilbert manifold and $p,q\in M$. In the coordinate H¹ topology (6.1),
--   $$
--   V_{p,q}\subseteq
--   \overline{\{c\in V_{p,q}:c\text{ is }C^\infty\}}.
--   $$
--   Thus every H¹ path from $p$ to $q$ can be approximated by smooth paths preserving both endpoints, in both uniform coordinate values and $L^2$ coordinate derivatives. This includes $p=q$. The density is the supporting result used to choose a smooth approximate geodesic.
--
--   Differences from the source:
--   - encoding: density among endpoint-fixed L₁² paths → inclusion of the full endpoint-fixed set in the closure of its smooth subset, for the explicitly defined topology (6.1); reason: this expresses relative density without choosing a metrization or changing the H¹ topology
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 341, Lemma 6.1 (PDF 18); https://doi.org/10.1016/0022-247X(74)90025-0

import Mathlib
import Definitions.Def_EkelandVP_Constraints_Supplement_riemannianManifold
import Definitions.Def_EkelandVP_Constraints_Supplement_sobolevPaths
set_option autoImplicit false

namespace EkelandVP.Constraints.Supplement

/-- Smooth paths are dense for (6.1), while both endpoints remain fixed. -/
theorem lemma_6_1 (D : CompleteStrongRiemannian) [ConnectedSpace D.M] (p q : D.M) :
    fixedEndpoints (H := D.H) p q ⊆
      closure {c : SobolevPaths D.H D.M | c ∈ fixedEndpoints p q ∧ SmoothPath c} := by sorry

end EkelandVP.Constraints.Supplement
