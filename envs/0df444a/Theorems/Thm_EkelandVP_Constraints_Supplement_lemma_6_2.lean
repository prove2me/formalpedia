-- Prove2me | Theorems.Thm_EkelandVP_Constraints_Supplement_lemma_6_2
-- name    : EkelandVP.Constraints.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:28:11.641895+00:00
-- url     : https://prove2.me/theorems/1a3b8b13-8d4b-4471-98b1-92c66af0565c
-- title:
--   Lemma 6.2 — the closed smooth fixed-endpoint path submanifold
-- statement:
--   Let $M$ be a connected complete strong smooth Riemannian Hilbert manifold and $p,q\in M$. The full H¹ fixed-endpoint path space
--   $$
--   V_{p,q}=\{c\in H^1([0,1];M):c(0)=p,\ c(1)=q\}
--   $$
--   is closed in $H^1([0,1];M)$ and is a split $C^\infty$ embedded submanifold for its canonical H¹ smooth structure. The conclusion contains both closedness and smooth local flattening to complemented linear subspaces; neither is assumed in the definition of an endpoint-fixed path. This provides the constraint manifold underlying the geodesic application.
--
--   Differences from the source:
--   - encoding: closed C∞ submanifold of the H¹ path manifold → closedness and canonical smooth local charts flattening the endpoint set to closed continuously complemented linear subspaces of H × L²; reason: the coordinate-family formulation specifies the canonical H¹ smooth structure and the split Hilbert submanifold meaning used by the source’s endpoint submersion argument on p.344
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 344, Lemma 6.2 (PDF 21); https://doi.org/10.1016/0022-247X(74)90025-0

import Mathlib
import Definitions.Def_EkelandVP_Constraints_Supplement_riemannianManifold
import Definitions.Def_EkelandVP_Constraints_Supplement_sobolevPaths
set_option autoImplicit false

namespace EkelandVP.Constraints.Supplement

/-- Both closedness and the full split smooth submanifold conclusion. -/
theorem lemma_6_2 (D : CompleteStrongRiemannian) [ConnectedSpace D.M] (p q : D.M) :
    IsClosed (fixedEndpoints (H := D.H) p q) ∧
      IsSplitH1Submanifold (fixedEndpoints (H := D.H) p q) := by sorry

end EkelandVP.Constraints.Supplement
