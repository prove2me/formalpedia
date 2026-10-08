-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_xc_extension_mono
-- name    : ExtensionComplexity.TSP.xc_extension_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:07:35.512926+00:00
-- url     : https://prove2.me/theorems/c88c44d5-9a71-4d52-88a4-7b1e25954381
-- title:
--   Lemma 9 (i) — if $F$ is an extension of $P$ then $\mathrm{xc}(F)\ge\mathrm{xc}(P)$
-- statement:
--   Let $P\subseteq\mathbb R^{\iota}$ and $F\subseteq\mathbb R^{\kappa}$ be polytopes. **Lemma 9 (i)**: if $F$ is an extension of $P$, i.e. $\pi(F)=P$ for some linear map $\pi$, then
--
--   $$\mathrm{xc}(F)\ \ge\ \mathrm{xc}(P).$$
--
--   Extension complexity can only drop under linear projection; this is how a lower bound for $\mathrm{COR}(n)$ becomes a lower bound for any polytope one of whose faces projects onto it.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:13, Lemma 9 (i)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_Polytope

namespace ExtensionComplexity.TSP

/-- **Lemma 9 (i)** (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:13): let `P` and `F` be
polytopes. If `F` is an extension of `P`, then `xc(F) ≥ xc(P)`. -/
theorem xc_extension_mono {ι κ : Type*} [Fintype ι] [Fintype κ] (P : Set (ι → ℝ))
    (F : Set (κ → ℝ)) (hP : IsPolytope P) (hF : IsPolytope F) (hext : IsExtension F P) :
    extensionComplexity P ≤ extensionComplexity F := by sorry

end ExtensionComplexity.TSP
