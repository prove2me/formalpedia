-- Prove2me | Theorems.Thm_CtxSearchTSR_eq_32
-- name    : CtxSearchTSR.eq_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:01.017037+00:00
-- url     : https://prove2.me/theorems/ecbc3ae1-20a0-4d7a-8b02-a7d3308d6ad9
-- title:
--   (32) — $\Phi(\mathbf m_+,R_+,\mathbf z)-\Phi(\mathbf m,R,\mathbf z)=\tfrac ra\bigl(\varphi(m^+,r^+,z)-\varphi(m,r,z)\bigr)$
-- statement:
--   Let $(\mathbf m,R)$ be a state with $R\succ0$, let $x\ne0$, $\mathbf z\in\mathbb R^d$ and $\varepsilon,Y\in\{-1,1\}$. Write $m=x^\top\mathbf m$, $z=x^\top\mathbf z$, $u=Rx$, $a=x^\top u$, $r=\|u\|_2$, let $(\mathbf m_+,R_+)$ be the update (10), $m^+=x^\top\mathbf m_+$ and $r^+=\|R_+x\|_2$. Then
--
--   $$\Phi(\mathbf m_+,R_+,\mathbf z)-\Phi(\mathbf m,R,\mathbf z)=\frac ra\bigl(\varphi(m^+,r^+,z)-\varphi(m,r,z)\bigr). \tag{32}$$
--
--   Here $\Phi$ is the potential (12) and $\varphi$ the one-dimensional potential of Lemma C.1. The identity reduces the $d$-dimensional potential drop to the scalar one.
--
--   Differences from the source:
--   - reading: the sentence has no hypothesis on x → x ≠ 0; reason: the proof of Lemma 2.5 treats x_t = 0 first ("the loss and potential change are both zero") and this step is in the "Otherwise" case, p.21; at x = 0 the quantities a and 1/a of the step are undefined
--   - generalization: (32) for the realized sign, the algorithm's answer and the fixed target with ‖z‖₂ ≤ 1 → for every e, Y ∈ {−1, 1} and every z ∈ ℝ^d; reason: the identity is algebraic and never uses how Y was produced or the norm of z; it specializes to the paper's case
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), App. C.3, proof of Lemma 2.5, p.22, (32)

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **Identity (32).** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), App. C.3, proof of Lemma 2.5, p.22.

"We first prove the identity Φ(m₊, R₊, z) − Φ(m, R, z) = r/a (φ(m⁺, r⁺, z) − φ(m, r, z))." (32)

On the left, **m**, **z** are vectors and Φ is (12); on the right, m = xᵀ**m**, z = xᵀ**z**,
m⁺ = xᵀ**m**₊, r = ‖R x‖₂, r⁺ = ‖R₊ x‖₂, a = xᵀR x, and φ is the potential of Lemma C.1.

**Formalization Note.** e, Y ∈ {−1, 1} independently (every realization); z is any vector; x ≠ 0
as in the proof (p.21). -/
theorem eq_32 {d : ℕ} (s : State d) (hR : s.R.PosDef) (x : Fin d → ℝ) (hx : x ≠ 0)
    (z : Fin d → ℝ) (e Y : ℝ) (he : e = 1 ∨ e = -1) (hY : Y = 1 ∨ Y = -1) :
    Phi (update s x e Y).m (update s x e Y).R z - Phi s.m s.R z =
      radius s.R x / quadA s.R x *
        (phi (x ⬝ᵥ (update s x e Y).m) (radius (update s x e Y).R x) (x ⬝ᵥ z) -
          phi (x ⬝ᵥ s.m) (radius s.R x) (x ⬝ᵥ z)) := by sorry

end CtxSearchTSR
