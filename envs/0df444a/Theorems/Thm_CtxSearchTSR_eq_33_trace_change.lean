-- Prove2me | Theorems.Thm_CtxSearchTSR_eq_33_trace_change
-- name    : CtxSearchTSR.eq_33_trace_change
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:27.200628+00:00
-- url     : https://prove2.me/theorems/e607c948-c68c-42bc-a49f-b600a6935671
-- title:
--   (33) — the trace change $\operatorname{Tr}(R_+-R)=\varepsilon Yr^2/(a(3-\varepsilon Y))=\tfrac ra(r^+-r)$
-- statement:
--   Let $(\mathbf m,R)$ be a state with $R\succ0$, let $x\ne0$, and let $\varepsilon,Y\in\{-1,1\}$. With $u=Rx$, $a=x^\top u$, $r=\|u\|_2$, $R_+$ the update (10) and $r^+=\|R_+x\|_2$,
--
--   $$\operatorname{Tr}(R_+-R)=\frac{\varepsilon Yr^2}{a(3-\varepsilon Y)}=\frac ra\,(r^+-r). \tag{33}$$
--
--   This is the trace part of identity (32).
--
--   Differences from the source:
--   - reading: the sentence has no hypothesis on x → x ≠ 0; reason: the proof of Lemma 2.5 treats x_t = 0 first ("the loss and potential change are both zero") and this step is in the "Otherwise" case, p.21; at x = 0 the quantities a and 1/a of the step are undefined
--   - generalization: (33) for the realized sign ε and the algorithm's answer Y = sign(xᵀz − P) → for every e, Y ∈ {−1, 1}; reason: each formula is an algebraic consequence of (10) that never uses how Y was produced; it specializes to the algorithm's answer
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), App. C.3, proof of Lemma 2.5, p.22, (33)

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **The trace change (33).** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), App. C.3, proof of Lemma 2.5, p.22.

"The trace change is Tr(R₊ − R) = εYr²/(a(3 − εY)) = r/a (r⁺ − r)." (33)

Here a = xᵀR x, r = ‖R x‖₂, R₊ is the update (10) and r⁺ = ‖R₊ x‖₂.

**Formalization Note.** e, Y ∈ {−1, 1} independently; x ≠ 0 as in the proof (p.21). -/
theorem eq_33_trace_change {d : ℕ} (s : State d) (hR : s.R.PosDef) (x : Fin d → ℝ)
    (hx : x ≠ 0) (e Y : ℝ) (he : e = 1 ∨ e = -1) (hY : Y = 1 ∨ Y = -1) :
    Matrix.trace ((update s x e Y).R - s.R) =
        e * Y * radius s.R x ^ 2 / (quadA s.R x * (3 - e * Y)) ∧
    e * Y * radius s.R x ^ 2 / (quadA s.R x * (3 - e * Y)) =
        radius s.R x / quadA s.R x * (radius (update s x e Y).R x - radius s.R x) := by sorry

end CtxSearchTSR
