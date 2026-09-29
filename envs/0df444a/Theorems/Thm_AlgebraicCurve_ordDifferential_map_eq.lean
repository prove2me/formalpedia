-- Prove2me | Theorems.Thm_AlgebraicCurve_ordDifferential_map_eq
-- name    : AlgebraicCurve.ordDifferential_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/0f844fd5-77bf-5dbe-bd96-684240788464
-- title:
--   Order of a pulled-back differential at a place (tame case)
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields with $F'$ integral over $F$ and the algebra structures compatible over $K$, and suppose both $F$ and $F'$ are curves over $K$ in the sense of `IsCurveOver`: principal divisors exist for every nonzero element, every place has residue field finite over $K$, and the module of Kähler differentials is free of rank one. Assume moreover that for every place $v$ of $F$ and every place $w$ of $F'$ — a place being a valuation subring containing the image of $K$, distinct from the whole field and a principal ideal ring — the differential $\mathrm{d}$ of a uniformizer spans the differentials, so that each $\omega$ has a coefficient $c_v(\omega)$ with $\omega = c_v(\omega)\,\mathrm{d}\pi_v$ and $\operatorname{ord}_v$ of that coefficient is the invariant $\operatorname{ordDifferential}$. Two further hypotheses are imposed: regularity, namely for every place $w$ of $F'$ and every nonzero $u \in F'$ with $\operatorname{ord}_w u = 0$ the coefficient of $\mathrm{d}u$ at $w$ is zero or has non-negative order at $w$; and tameness, namely the ramification index $e_w = e(w \mid w|_F)$, defined as the least positive value of $\operatorname{ord}_w$ on nonzero elements of $F$, is nonzero in $F'$. Then for every nonzero $\omega_0 \in \Omega_{F/K}$ and every place $w$ of $F'$, the image of $\omega_0$ under the functoriality map $\Omega_{F/K} \to \Omega_{F'/K}$ satisfies $\operatorname{ordDifferential}_w = e_w \cdot \operatorname{ordDifferential}_{w|_F}(\omega_0) + (e_w - 1)$, where $w|_F$ is the place of $F$ obtained by pulling the valuation subring back along $F \to F'$.
--
--   This is the local computation underlying the different in the tame case, the per-place ingredient of the Riemann–Hurwitz comparison of canonical divisors for a covering of curves. It feeds the comparison of canonical divisors and regular differentials, and is used in the surjectivity criterion for the structure map over an algebraically closed base and in the treatment of regular differentials on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ordDifferential_map_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem ordDifferential_map_eq {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (w : Place K F') :
    w.ordDifferential (KaehlerDifferential.map K K F F' ω₀)
      = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀
          + ((w.ramificationIndex F : ℤ) - 1) := by sorry
