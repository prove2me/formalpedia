-- Prove2me | Theorems.Thm_AffineStorage_Ruin_eq_9
-- name    : AffineStorage.Ruin.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:29.262177+00:00
-- url     : https://prove2.me/theorems/a785e836-5936-4858-bfba-dbcdfb88c7f2
-- title:
--   Eq. (9), p. 1287 (PDF 8) — φ(ϑ) = −(∫_ϑ^∞ G(η) e^{−F⋆(η)} dη) e^{F⋆(ϑ)}
-- statement:
--   Let $\varphi$ be the transform of the expected discounted penalty at ruin and $F,G$ the functions of Proposition 1, with $G$ built from the model's constants $\varrho(0)$ and $\varphi(\mu)$. Let $F_\star$ be any primitive of $F$ on $(0,\mu)\cup(\mu,\infty)$. For every $\vartheta>0$ with $\vartheta\ne\mu$,
--   $$\varphi(\vartheta)=-\Big(\int_\vartheta^\infty G(\eta)\exp(-F_\star(\eta))\,d\eta\Big)\exp(F_\star(\vartheta)).\tag{9}$$
--
--   This is the solution of (6) singled out by the boundedness of $\varphi$ at infinity, where $F_\star\to\infty$. Together with (12), which determines the two constants in $G$, it is the closed form of Theorem 1.
--
--   **Formalization Note.** For $\vartheta<\mu$ the integral crosses the singular point $\mu$. The right-hand side then does not depend on the constant that $F_\star$ carries on $(\mu,\infty)$ because $I(\mu)=0$ (eq. (11)).
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1287 (PDF 8), eqs. (8)–(9)

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem eq_9 (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (Fs : ℝ → ℝ) (hF : IsPrimitiveF P Fs) :
    ∀ ϑ, 0 < ϑ → ϑ ≠ P.μ →
      phi B P ϑ = -(∫ η in Set.Ioi ϑ,
          G P (rho B P 0) (phi B P P.μ) η * Real.exp (-(Fs η))) * Real.exp (Fs ϑ) := by sorry

end AffineStorage.Ruin
