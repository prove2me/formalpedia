-- Prove2me | Theorems.Thm_EllipsoidFitting_proposition_3_2
-- name    : EllipsoidFitting.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:29.067223+00:00
-- url     : https://prove2.me/theorems/6520574b-7118-431e-8e24-d36c3bd83080
-- title:
--   Proposition 3.2 — a dual witness $\Lambda\succeq0$, $\Lambda\in S$, $\langle\Lambda,I-R\rangle<0$ refutes ellipsoid fitting
-- statement:
--   Let $v_1,\dots,v_m\in\mathbb R^d$ have invertible Gram matrix $M$ and let $R=L^*M^{-1}\eta$. If a matrix $\Lambda$ satisfies
--
--   1. $\Lambda\succeq0$,
--   2. $\Lambda\in S=\operatorname{span}\{v_iv_i^\top:i\in[m]\}$,
--   3. $\langle\Lambda,I-R\rangle=\operatorname{Tr}\bigl(\Lambda(I-R)\bigr)<0$,
--
--   then there is no positive semidefinite $X$ with $v_i^\top Xv_i=1$ for all $i$.
--
--   This is weak duality for the ellipsoid fitting SDP; the refutation side of the main theorem constructs such a $\Lambda$.
--
--   Differences from the source:
--   - encoding: R = L*M⁻¹η with M⁻¹ → hypothesis det M a unit; reason: only excludes the case where R is undefined
--   - encoding: such a solution Λ (Proposition 3.1) → hypotheses Λ PSD, Λ ∈ span{v_iv_iᵀ}, Tr(Λ(I − R)) < 0; reason: the definition of a dual solution in Proposition 3.1
--   - encoding: refutes the existence of a fitting ellipsoid → ¬ Fits v; reason: Fits is the PSD fitting predicate of p.2
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Propositions 3.1–3.2, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_EllipsoidFitting_Fits
import Definitions.Def_EllipsoidFitting_perturbR

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **Proposition 3.2 (the dual witness refutes).** de la Cerda, Potechin, Tulsiani, Xu, *Sharp
Phase Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Propositions
3.1–3.2, p.35: "The dual of ellipsoid fitting is given by Λ ⪰ 0 such that Λ ∈ S := span{viv⊤_i :
i ∈ [m]}, ⟨Λ, I − R⟩ < 0 where … ⟨A, B⟩ = Tr(A · B)." and "Such a solution Λ refutes the
existence of a fitting ellipsoid."

If `M` is invertible and some PSD `Λ ∈ span{v_i v_iᵀ}` has `Tr(Λ(I − R)) < 0`, then no
(possibly degenerate) ellipsoid passes through the points.

**Formalization Note** `R = L*M⁻¹η` uses `M⁻¹`, so `M` invertible is a hypothesis. -/
theorem proposition_3_2 {m d : ℕ} (v : Fin m → Fin d → ℝ) (hM : IsUnit (gram v).det)
    (Λ : Matrix (Fin d) (Fin d) ℝ) (hΛ : Λ.PosSemidef) (hS : Λ ∈ imageS v)
    (htr : (Λ * (1 - perturbR v)).trace < 0) : ¬ Fits v := by sorry

end EllipsoidFitting
