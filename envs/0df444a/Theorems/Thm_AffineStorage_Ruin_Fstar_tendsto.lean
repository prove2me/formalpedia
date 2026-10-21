-- Prove2me | Theorems.Thm_AffineStorage_Ruin_Fstar_tendsto
-- name    : AffineStorage.Ruin.Fstar_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:26.931112+00:00
-- url     : https://prove2.me/theorems/5f7cc1cf-23cc-4af3-b3b3-a96ba47426f9
-- title:
--   §2.3, p. 1287 (PDF 8) — F(ϑ) → p/r, and F⋆ → ∞ as ϑ → ∞, ϑ ↓ 0, ϑ ↑ μ, ϑ ↓ μ
-- statement:
--   Let $F$ be the coefficient function of Proposition 1,
--   $$F(\vartheta)=\frac pr-\frac{\lambda_-}r\frac{1-\delta(\vartheta)}\vartheta+\frac{\lambda_+}r\frac1{\mu-\vartheta}-\frac{\alpha+\nu}{r\vartheta},$$
--   and let $F_\star$ be any primitive of $F$ on $(0,\mu)\cup(\mu,\infty)$. Then:
--
--   1. $F(\vartheta)\to p/r$ as $\vartheta\to\infty$;
--   2. $F_\star(\vartheta)\to\infty$ as $\vartheta\to\infty$;
--   3. $F_\star(\vartheta)\to\infty$ as $\vartheta\downarrow0$;
--   4. $F_\star(\vartheta)\to\infty$ as $\vartheta\uparrow\mu$;
--   5. $F_\star(\vartheta)\to\infty$ as $\vartheta\downarrow\mu$.
--
--   These limits force the boundary conditions that pin down the solution of (6). The limit at $\infty$ gives (8)–(9), the limit at $0$ gives $I(0)=0$, and the limits at $\mu$ give $I(\mu)=0$.
--
--   **Formalization Note.** The page states parts 2–4. Part 5 is the case "dealt with analogously" in Remark 3, and it is needed for (11). The page's sharper forms $\lim_{\vartheta\downarrow0}F_\star(\vartheta)/\log\vartheta=D_0<0$ are not stated: without a moment condition on the claims, which the paper never assumes, they can fail. The divergence holds without one.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1287 (PDF 8), §2.3; p. 1288 (PDF 9), Remark 3

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem Fstar_tendsto (P : Params) (hS : P.Standing) (Fs : ℝ → ℝ)
    (hF : IsPrimitiveF P Fs) :
    Tendsto (F P) atTop (𝓝 (P.p / P.r)) ∧
    Tendsto Fs atTop atTop ∧
    Tendsto Fs (𝓝[>] 0) atTop ∧
    Tendsto Fs (𝓝[<] P.μ) atTop ∧
    Tendsto Fs (𝓝[>] P.μ) atTop := by sorry

end AffineStorage.Ruin
