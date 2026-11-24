-- Prove2me | Theorems.Thm_Arxiv1506_07229_negative_static_permittivity_violates_KK
-- name    : Arxiv1506_07229.negative_static_permittivity_violates_KK
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:02:16.533188+00:00
-- url     : https://prove2.me/theorems/58ed4a2e-79a2-47f1-8e41-d0e6f12ac3fa
-- title:
--   Eq. (5): a negative static permittivity violates the Kramers-Kronig relations
-- statement:
--   Let $R:\mathbb{R}\to\mathbb{C}$ be a response function of real frequency, here $R(\omega)=\varepsilon(q,\omega)$. Suppose that $R(\omega)\to1$ as $\omega\to+\infty$, and that $\operatorname{Im}R(\omega)\ge0$ for all $\omega\ge0$. If the static value is negative,
--
--   $$\operatorname{Re}R(0)<0,$$
--
--   then $R$ does not satisfy the Kramers-Kronig relations (5).
--
--   This is the paper's argument that the negative static permittivity of graphene above $q_c$ is incompatible with KK relations for $\varepsilon$. At $\omega=0$ the first relation would give $\operatorname{Re}R(0)=1+\frac2\pi\int_0^\infty\operatorname{Im}R(\omega')/\omega'\,d\omega'\ge1$.
--
--   **Formalization Note** The principal value is the limit as $\delta\to0^+$ of the integral over $(0,\infty)$ with $(\omega-\delta,\omega+\delta)$ removed. If such an integral does not exist, Lean gives it the value $0$. This only enlarges the set of functions that count as satisfying the KK relations, so the conclusion that they fail is not weakened.
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), claim c024; main text after Fig. 3, Eq. (5), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem negative_static_permittivity_violates_KK (R : ℝ → ℂ)
    (hinf : Tendsto R atTop (𝓝 1)) (him : ∀ ω : ℝ, 0 ≤ ω → 0 ≤ (R ω).im)
    (hneg : (R 0).re < 0) :
    ¬ KKRelations R := by sorry

end Arxiv1506_07229
