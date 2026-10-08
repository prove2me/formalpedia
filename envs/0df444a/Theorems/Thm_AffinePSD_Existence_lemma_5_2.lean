-- Prove2me | Theorems.Thm_AffinePSD_Existence_lemma_5_2
-- name    : AffinePSD.Existence.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:13.782174+00:00
-- url     : https://prove2.me/theorems/071052c9-3091-479f-9070-d175ab908b5c
-- title:
--   Lemma 5.2 — the growth bound ⟨u, R(u)⟩ ≤ (K/2)(‖u‖² + 1) on S_d^+
-- statement:
--   Let $(\alpha,b,\beta^{ij},c,\gamma,m,\mu)$ satisfy every condition of Definition 2.3 except possibly (2.4), and let $R$ be the function (2.17). Then there is a constant $K$ such that
--   $$\langle u,R(u)\rangle\le\frac K2\big(\|u\|^2+1\big),\qquad u\in S_d^+.\tag{5.1}$$
--
--   With Gronwall's inequality this rules out blow-up of the Riccati flow in finite time.
--
--   **Formalization Note** $\|\cdot\|$ is the norm of the trace pairing. The hypothesis omits (2.4), so the statement is stronger than the page. $K$ may depend on the parameters and on $\chi$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 5.2, (5.1), p. 38

import Mathlib
import Definitions.Def_AffinePSD_Existence_Params

namespace AffinePSD.Existence

/-- Lemma 5.2 (arXiv:0910.0137v3, §5.1, p. 38), (5.1): there is a constant `K` with
`⟨u, R(u)⟩ ≤ (K/2)(‖u‖² + 1)` for all `u ∈ S_d^+`.
Formalization Note: `‖·‖` is the norm of the trace pairing (`fnorm`); hypothesis `AdmissibleCore`
(Definition 2.3 without (2.4)), weaker than the section's standing admissibility; `K` depends on the
parameter set and the truncation function, as on the page. -/
theorem lemma_5_2 {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (hP : AffinePSD.Necessity.AdmissibleCore χ P) :
    ∃ K : ℝ, ∀ u, PSD u → tr u (AffinePSD.Necessity.Rpar χ P u) ≤ K / 2 * (fnorm u ^ 2 + 1) := by sorry

end AffinePSD.Existence
