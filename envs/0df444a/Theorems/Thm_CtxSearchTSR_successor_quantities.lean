-- Prove2me | Theorems.Thm_CtxSearchTSR_successor_quantities
-- name    : CtxSearchTSR.successor_quantities
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:12.067722+00:00
-- url     : https://prove2.me/theorems/eb7c3be7-de6e-4e6c-80d6-af9b74f58205
-- title:
--   Proof of Lemma 2.5, p.22 — the projected successor quantities $m^+=m+Yr/(3-\varepsilon Y)$, $R_+x=\tfrac3{3-\varepsilon Y}Rx$, $r^+=3r/(3-\varepsilon Y)$
-- statement:
--   Let $(\mathbf m,R)$ be a state with $R\succ0$, let $x\ne0$, and let $\varepsilon,Y\in\{-1,1\}$. Write $m=x^\top\mathbf m$, $u=Rx$, $a=x^\top u$, $r=\|u\|_2$, and let $(\mathbf m_+,R_+)$ be the update (10). Then
--
--   $$m^+:=x^\top\mathbf m_+=m+\frac{Yr}{3-\varepsilon Y},\qquad R_+x=\frac{3}{3-\varepsilon Y}Rx,\qquad r^+:=\|R_+x\|_2=\frac{3r}{3-\varepsilon Y}.$$
--
--   So the projected mean and deviation proxies evolve exactly as $m^+$ and $r^+$ in Lemma C.1.
--
--   Differences from the source:
--   - reading: the sentence has no hypothesis on x → x ≠ 0; reason: the proof of Lemma 2.5 treats x_t = 0 first ("the loss and potential change are both zero") and this step is in the "Otherwise" case, p.21; at x = 0 the quantities a and 1/a of the step are undefined
--   - generalization: the formulas for the realized sign ε and the algorithm's answer Y = sign(xᵀz − P) → for every e, Y ∈ {−1, 1}; reason: each formula is an algebraic consequence of (10) that never uses how Y was produced; it specializes to the algorithm's answer
--   - reading: "Thus m+, r+ are exactly the successor quantities in Lemma C.1" → no separate clause; reason: the right-hand sides are literally Lemma C.1's m⁺ and r⁺; the sentence is a remark
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), App. C.3, proof of Lemma 2.5, p.22

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **The projected successor quantities.** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), App. C.3, proof of Lemma 2.5,
p.22.

"For a realization of the random sign and the answer, let m₊, R₊ be the updated state. The update
formulas imply m⁺ = xᵀm₊ = m + Yr/(3 − εY), R₊x = 3/(3 − εY) Rx, r⁺ = ‖R₊x‖₂ = 3r/(3 − εY)."

Here m = xᵀ**m** and r = ‖R x‖₂ at the current state, and (**m**₊, R₊) is the update (10).

**Formalization Note.** The sign e and the answer Y range over {−1, 1} independently (every
realization). x ≠ 0 as in the proof ("Otherwise", p.21). -/
theorem successor_quantities {d : ℕ} (s : State d) (hR : s.R.PosDef) (x : Fin d → ℝ)
    (hx : x ≠ 0) (e Y : ℝ) (he : e = 1 ∨ e = -1) (hY : Y = 1 ∨ Y = -1) :
    x ⬝ᵥ (update s x e Y).m = x ⬝ᵥ s.m + Y * radius s.R x / (3 - e * Y) ∧
    (update s x e Y).R *ᵥ x = (3 / (3 - e * Y)) • (s.R *ᵥ x) ∧
    radius (update s x e Y).R x = 3 * radius s.R x / (3 - e * Y) := by sorry

end CtxSearchTSR
