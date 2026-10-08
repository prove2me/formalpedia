-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_xc_face_mono
-- name    : ExtensionComplexity.TSP.xc_face_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:07:57.213052+00:00
-- url     : https://prove2.me/theorems/6fb0bd87-7b01-4234-b6e1-78ba97083591
-- title:
--   Lemma 9 (ii) — if $F$ is a face of $Q$ then $\mathrm{xc}(Q)\ge\mathrm{xc}(F)$
-- statement:
--   Let $Q,F\subseteq\mathbb R^{\kappa}$ be polytopes. **Lemma 9 (ii)**: if $F$ is a face of $Q$ (either $Q$ itself or the intersection of $Q$ with a valid hyperplane), then
--
--   $$\mathrm{xc}(Q)\ \ge\ \mathrm{xc}(F).$$
--
--   A face is never harder to describe than the whole polytope. Together with part (i) it reduces lower bounds for $\mathrm{TSP}(q)$ and $\mathrm{STAB}(H_n)$ to the lower bound for $\mathrm{COR}(n)$.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:13, Lemma 9 (ii)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_Polytope

namespace ExtensionComplexity.TSP

/-- **Lemma 9 (ii)** (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:13): let `Q` and `F` be
polytopes. If `F` is a face of `Q`, then `xc(Q) ≥ xc(F)`. -/
theorem xc_face_mono {κ : Type*} [Fintype κ] (Q F : Set (κ → ℝ)) (hQ : IsPolytope Q)
    (hF : IsPolytope F) (hface : IsFace Q F) :
    extensionComplexity F ≤ extensionComplexity Q := by sorry

end ExtensionComplexity.TSP
