-- Prove2me | Theorems.Thm_CourierDispatch_Exogenous_dedicated_trip_moments
-- name    : CourierDispatch.Exogenous.dedicated_trip_moments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:17.55198+00:00
-- url     : https://prove2.me/theorems/24d788d6-6db5-4ab1-8ba7-794735281eba
-- title:
--   (3), p. 10 — the dedicated trip X_D = 2‖U‖ has E[X_D] = 4r/3 and E[X_D²] = 2r², giving μ_D (4) and C_D (6)
-- statement:
--   Let $r>0$ and let $U$ be uniformly distributed on the disk of radius $r$ centred at the facility. Under dedicated delivery the trip length is the round trip $X_D=2\|U\|$. Then $X_D$ and $X_D^2$ are integrable, and
--   $$\mathbb E[X_D]=\frac43 r,\qquad \mathbb E[X_D^2]=2r^2,$$
--   and consequently
--   $$\frac1{\mathbb E[X_D]}=\frac3{4r}=\mu_D,\qquad 1+\frac{\mathbb E[X_D^2]-(\mathbb E[X_D])^2}{(\mathbb E[X_D])^2}=\frac98=C_D .$$
--
--   This grounds the constants $\mu_D$ and $C_D$ of the dedicated wait $W_D$ in the geometry of the disk.
--
--   **Formalization Note** The paper writes these expectations as iterated integrals after the substitution $x=\|u\|^2$; the Lean states the expectations themselves as Bochner integrals of $2\|x\|$ and $(2\|x\|)^2$ against the uniform law on the disk.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), p. 10, (3), (4), (6)

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting
import Definitions.Def_CourierDispatch_Exogenous_DiskLaw

namespace CourierDispatch.Exogenous

/-- (3), p. 10: the dedicated round-trip length `X_D = 2‖U‖`, `U` uniform on the disk of radius `r`,
is integrable with integrable square, and has `E[X_D] = 4r/3` and `E[X_D²] = 2r²`; hence `μ_D = 1/E[X_D]` (4) and
`C_D = 1 + (E[X_D²] − E[X_D]²)/E[X_D]²` (6). -/
theorem dedicated_trip_moments (r : ℝ) (hr : 0 < r) :
    MeasureTheory.Integrable (fun x => 2 * ‖x‖) (diskLaw r) ∧
    MeasureTheory.Integrable (fun x => (2 * ‖x‖) ^ 2) (diskLaw r) ∧
    (∫ x, 2 * ‖x‖ ∂(diskLaw r)) = 4 / 3 * r ∧
    (∫ x, (2 * ‖x‖) ^ 2 ∂(diskLaw r)) = 2 * r ^ 2 ∧
    1 / (∫ x, 2 * ‖x‖ ∂(diskLaw r)) = muD r ∧
    1 + ((∫ x, (2 * ‖x‖) ^ 2 ∂(diskLaw r)) - (∫ x, 2 * ‖x‖ ∂(diskLaw r)) ^ 2) /
      (∫ x, 2 * ‖x‖ ∂(diskLaw r)) ^ 2 = CD := by sorry

end CourierDispatch.Exogenous
