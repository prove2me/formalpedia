-- Prove2me | Theorems.Thm_AffinePSD_Necessity_lemma_3_1
-- name    : AffinePSD.Necessity.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:24.662999+00:00
-- url     : https://prove2.me/theorems/026e9951-3bb4-4e1b-93a8-0ad985714dcb
-- title:
--   Lemma 3.1 — a PSD matrix below a boundary point of $S_d^+$ lies on the boundary
-- statement:
--   Let $u \in \partial S_d^+ = S_d^+ \setminus S_d^{++}$ and let $v \in S_d^+$ with $v \preceq u$, i.e. $u - v \in S_d^+$. Then
--   $$v \in \partial S_d^+.$$
--
--   This elementary observation about the order on the cone is what turns order preservation of $\psi$ into a statement about the boundary in the proof that $\psi(t,\cdot)$ maps $S_d^{++}$ into itself (Lemma 3.3).
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 3.1, p. 15

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

namespace AffinePSD.Necessity

/-- Lemma 3.1 (Cuchiero, Filipović, Mayerhofer, Teichmann, arXiv:0910.0137v3, §3, p. 15):
if `u ∈ ∂S_d^+` and `S_d^+ ∋ v ⪯ u`, then `v ∈ ∂S_d^+`.

**Formalization Note.** `∂S_d^+ = S_d^+ ∖ S_d^{++}` is `PSD ∧ ¬ PD`; `v ⪯ u` is `PSD (u − v)`. -/
theorem lemma_3_1 {d : ℕ} (u v : Mat d) (hu : PSD u) (hu' : ¬ PD u) (hv : PSD v)
    (hvu : PSD (u - v)) : PSD v ∧ ¬ PD v := by sorry

end AffinePSD.Necessity
