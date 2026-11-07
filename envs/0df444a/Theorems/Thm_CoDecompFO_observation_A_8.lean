-- Prove2me | Theorems.Thm_CoDecompFO_observation_A_8
-- name    : CoDecompFO.observation_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:36.49497+00:00
-- url     : https://prove2.me/theorems/39cb4d72-7ff1-4b9e-9b87-5d45842f0713
-- title:
--   Observation A.8 — $\lim(T^\circ)=(\lim T)^\circ$
-- statement:
--   Let $\mathcal T$ be a tree co-decomposition. Then
--   $$
--   \lim(\mathcal T^\circ)=(\lim\mathcal T)^\circ .
--   $$
--   The two structures have the same matching families, and $\circ$ on the limit of $\mathcal T^\circ$, which holds coordinatewise in every bag, is equality of matching families.
--
--   This is why a program may evaluate equality by a linear pre-processing of the bags, instead of constructing the limit.
--
--   Differences from the source:
--   - encoding: the equality of structures lim(T°) = (lim T)° → an isomorphism that keeps every coordinate of a matching family; reason: the two point sets are different Lean types that have the same coordinates
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Observation A.8, p.53

import Mathlib
import Definitions.Def_CoDecompFO_Lim

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Observation A.8** (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…, p.53): "Let T be
a co-decomposition. Then lim(T°) = (lim(T))°."

**Formalization Note** The equality is the isomorphism that keeps every coordinate of a matching
family. The content is that `∘` on the limit is equality of matching families. -/
theorem observation_A_8 {σ : Sig} (T : CoDecomp σ) :
    ∃ u : T.withEq.Lim ≃[(sigmaEq σ).lang] Circ σ T.Lim,
      ∀ (x : T.withEq.Lim) (t : Fin T.b),
        CoDecomp.Lim.val (T := T) (u x) t = x.val t := by sorry

end CoDecompFO
