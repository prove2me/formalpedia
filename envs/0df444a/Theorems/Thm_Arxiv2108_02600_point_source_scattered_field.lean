-- Prove2me | Theorems.Thm_Arxiv2108_02600_point_source_scattered_field
-- name    : Arxiv2108_02600.point_source_scattered_field
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:17:19.3627+00:00
-- url     : https://prove2.me/theorems/e14e798e-51b4-5b57-b98a-95acbbc71331
-- title:
--   Example 2, eq. (5.5): exact scattered field of a point source below the surface
-- statement:
--   Let $f\in B^{(0)}_{c,M}$ ($M>0$) and let $z=(0,-3)$ lie below $\Gamma$, i.e. $f(0)>-3$. Let $q=(0.6,0.8)$ and $u^{\rm inc}_3(x)=G(x,z)q$ (5.4). Then the scattered field of (DP) with data $g=-u^{\rm inc}_3|_\Gamma$ is
--
--   $$u^{\rm sc}_3(x)=-G(x,z)q,\qquad x\in\Omega\qquad(5.5).$$
--
--   So $-G(\cdot,z)q$ solves (DP) with this data, and every solution of (DP) with this data coincides with it on $\Omega$.
--
--   **Formalization Note** The paper justifies (5.5) only by well-posedness of (DP). It does not show that $-G(\cdot,z)q$ satisfies (2.3) and (2.8). The statement covers every surface of the class with $z$ below it, which includes Examples 2 and 3.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c014; Section 5, Example 2, eqs. (5.4)-(5.5), PDF p. 18

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem point_source_scattered_field (P : Lame) (c M : ℝ) (hM : 0 < M) (f : ℝ → ℝ)
    (hf : InB 0 c M f) (hz : -3 < f 0) :
    let z : Pt := ![0, -3]
    let q : Fin 2 → ℂ := ![3 / 5, 4 / 5]
    let uinc : Pt → Fin 2 → ℂ := fun x => (greenFree P x z).mulVec q
    IsDPSolution P f (fun x => -uinc x) (fun x => -uinc x) ∧
      ∀ v : Pt → Fin 2 → ℂ, IsDPSolution P f (fun x => -uinc x) v →
        ∀ x ∈ domainAbove f, v x = -uinc x := by sorry

end Arxiv2108_02600
