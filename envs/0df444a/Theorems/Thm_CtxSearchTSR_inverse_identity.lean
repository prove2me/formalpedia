-- Prove2me | Theorems.Thm_CtxSearchTSR_inverse_identity
-- name    : CtxSearchTSR.inverse_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:03.575886+00:00
-- url     : https://prove2.me/theorems/5bea1662-4934-4efa-bb2d-4f073115debd
-- title:
--   Proof of Lemma 2.5, p.22 — $\mathbf m_+-\mathbf m=\tfrac\delta a u$ and $R_+^{-1}=R^{-1}-\tfrac{\varepsilon Y}{3a}xx^\top$
-- statement:
--   Let $(\mathbf m,R)$ be a state with $R\succ0$, let $x\ne0$, and let $\varepsilon,Y\in\{-1,1\}$. With $u=Rx$, $a=x^\top u$, $r=\|u\|_2$, $\delta=Yr/(3-\varepsilon Y)$ and $(\mathbf m_+,R_+)$ the update (10),
--
--   $$\mathbf m_+-\mathbf m=\frac\delta a\,u,\qquad R_+^{-1}=R^{-1}-\frac{\varepsilon Y}{3a}\,xx^\top.$$
--
--   The second identity is the Sherman–Morrison step for the rank-one update of (10); it gives the quadratic part of identity (32).
--
--   **Formalization Note** $R_+^{-1}$ is Mathlib's matrix inverse.
--
--   Differences from the source:
--   - reading: the sentence has no hypothesis on x → x ≠ 0; reason: the proof of Lemma 2.5 treats x_t = 0 first ("the loss and potential change are both zero") and this step is in the "Otherwise" case, p.21; at x = 0 the quantities a and 1/a of the step are undefined
--   - generalization: the identities for the realized sign ε and the algorithm's answer Y = sign(xᵀz − P) → for every e, Y ∈ {−1, 1}; reason: each formula is an algebraic consequence of (10) that never uses how Y was produced; it specializes to the algorithm's answer
--   - reading: "εY/3a" → εY/(3a); reason: the only reading under which R₊ times the right-hand side is the identity ("follows directly by multiplication with R+")
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), App. C.3, proof of Lemma 2.5, p.22

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **The update of the mean and of the inverse scale matrix.** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), App. C.3,
proof of Lemma 2.5, p.22.

"For the quadratic term, write δ = m⁺ − m = Yr/(3 − εY). The updates give
m₊ − m = δ/a u, R₊⁻¹ = R⁻¹ − εY/3a xxᵀ."

Here **u** = R x, a = xᵀR x, r = ‖R x‖₂ and (**m**₊, R₊) is the update (10).

**Formalization Note.** "εY/3a" is read εY/(3a), the only reading under which R₊ times the right
side is the identity. R⁻¹ is Mathlib's `Matrix.inv`. e, Y ∈ {−1, 1} independently; x ≠ 0 as in the
proof (p.21). -/
theorem inverse_identity {d : ℕ} (s : State d) (hR : s.R.PosDef) (x : Fin d → ℝ)
    (hx : x ≠ 0) (e Y : ℝ) (he : e = 1 ∨ e = -1) (hY : Y = 1 ∨ Y = -1) :
    (update s x e Y).m - s.m =
        ((Y * radius s.R x / (3 - e * Y)) / quadA s.R x) • dirU s.R x ∧
    ((update s x e Y).R)⁻¹ = s.R⁻¹ - (e * Y / (3 * quadA s.R x)) • vecMulVec x x := by sorry

end CtxSearchTSR
