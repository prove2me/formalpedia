-- Prove2me | Theorems.Thm_AffineStorage_Ruin_remark_3
-- name    : AffineStorage.Ruin.remark_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:37.822149+00:00
-- url     : https://prove2.me/theorems/386f209a-9716-439e-a874-f67bd1a5e149
-- title:
--   Remark 3, p. 1288 (PDF 9) — the integrals I_k in (10) and (11) are finite
-- statement:
--   Let $F_\star$ be any primitive, on $(0,\mu)\cup(\mu,\infty)$, of the coefficient function $F$ of Proposition 1, and let
--   $$G_1(\eta)=-\frac pr,\qquad G_2(\eta)=-\frac{\lambda_+}r\frac1{\mu-\eta},\qquad G_3(\eta)=\frac{\lambda_-}r\frac{\delta(\beta)-\delta(\eta+\gamma)}{\eta+\gamma-\beta}.$$
--   At the removable singularity $\eta=\beta-\gamma$, $G_3$ takes its limit value. Then for $k=1,2,3$ the function $\eta\mapsto G_k(\eta)\exp(-F_\star(\eta))$ is Lebesgue integrable on $(0,\infty)$.
--
--   Hence all the integrals $I_k(\vartheta)=\int_\vartheta^\infty G_k(\eta)e^{-F_\star(\eta)}\,d\eta$ for $\vartheta\ge0$ are finite, in particular $I_k(0)$ and $I_k(\mu)$. These are the coefficients and right-hand sides of the linear system (10)–(11). Integrability across $\eta=\mu$ holds despite the pole of $G_2$ there.
--
--   **Formalization Note.** The page argues finiteness assuming that $G_k$ is bounded near $0$ and that $F_\star(\eta)=-\chi_0\log\eta+\bar\chi_0(\eta)$ with $\bar\chi_0$ bounded. Without moments of the claims both can fail. The statement asserts only the integrability, which holds without moment assumptions.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1288 (PDF 9), Remark 3

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem remark_3 (P : Params) (hS : P.Standing) (Fs : ℝ → ℝ)
    (hF : IsPrimitiveF P Fs) :
    IntegrableOn (fun η => G1 P η * Real.exp (-(Fs η))) (Set.Ioi 0) ∧
    IntegrableOn (fun η => G2 P η * Real.exp (-(Fs η))) (Set.Ioi 0) ∧
    IntegrableOn (fun η => G3 P η * Real.exp (-(Fs η))) (Set.Ioi 0) := by sorry

end AffineStorage.Ruin
