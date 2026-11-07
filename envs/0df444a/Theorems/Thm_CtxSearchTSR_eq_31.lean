-- Prove2me | Theorems.Thm_CtxSearchTSR_eq_31
-- name    : CtxSearchTSR.eq_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:59.548967+00:00
-- url     : https://prove2.me/theorems/ae7689c1-08dc-4f9f-aa1b-95c347886980
-- title:
--   (31) — $0<a=x^\top u\le\|x\|_2\|u\|_2\le r$
-- statement:
--   Let $R\succ0$ and $x\in\mathbb R^d$ with $x\ne0$ and $\|x\|_2\le1$. With $u=Rx$, $a=x^\top u=x^\top Rx$ and $r=\|u\|_2$,
--
--   $$0<a=x^\top u\le\|x\|_2\|u\|_2\le r. \tag{31}$$
--
--   This converts the factor $r/a$ of identity (32) into the factor $\ge1$ used to compare the potential drop with the loss.
--
--   **Formalization Note** $a$ is defined as $x^\top u$, so the equality $a=x^\top u$ holds by definition; the three stated clauses are $0<a$, $a\le\|x\|_2\|u\|_2$ and $\|x\|_2\|u\|_2\le r$.
--
--   Differences from the source:
--   - reading: the sentence has no hypothesis on x → x ≠ 0; reason: the proof of Lemma 2.5 treats x_t = 0 first ("the loss and potential change are both zero") and this step is in the "Otherwise" case, p.21; at x = 0 the quantities a and 1/a of the step are undefined
--   - encoding: 0 < a = x⊤u → a is defined as xᵀu, so the equality is definitional and not a separate clause; reason: Lean convention; same content
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), App. C.3, proof of Lemma 2.5, p.22, (31)

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **Inequality (31).** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), App. C.3, proof of Lemma 2.5, p.22.

"Since R ≻ 0 and ‖x‖₂ ≤ 1, we have 0 < a = xᵀu ≤ ‖x‖₂‖u‖₂ ≤ r." (31)

**Formalization Note.** u = R x (`dirU`), a = xᵀu (`quadA`, definitionally xᵀR x), r = ‖u‖₂
(`radius`), all Euclidean. x ≠ 0 is the case the proof is in ("For x_t = 0 … Otherwise", p.21). -/
theorem eq_31 {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosDef) (x : Fin d → ℝ)
    (hx : x ≠ 0) (hx1 : eucNorm x ≤ 1) :
    0 < quadA R x ∧ quadA R x ≤ eucNorm x * eucNorm (dirU R x) ∧
      eucNorm x * eucNorm (dirU R x) ≤ radius R x := by sorry

end CtxSearchTSR
