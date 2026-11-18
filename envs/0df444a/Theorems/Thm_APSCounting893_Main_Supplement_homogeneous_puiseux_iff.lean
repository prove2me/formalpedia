-- Prove2me | Theorems.Thm_APSCounting893_Main_Supplement_homogeneous_puiseux_iff
-- name    : APSCounting893.Main.Supplement.homogeneous_puiseux_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T21:10:34.834183+00:00
-- url     : https://prove2.me/theorems/aaed1883-e098-4d2f-8af7-87d8e99ec913
-- title:
--   Theorem 4.7 — Normalized homogeneous Puiseux witnesses for APS
-- statement:
--   Let $F:\mathbb C^n\to\mathbb C^{n+1}$ be a reduced map with $n\ge1$, image dimension $n$ and degree bound $d\ge2$. Fix the published admissible normalization, good open subset and nonzero line direction, and admissible homogenizing degrees $\max(1,\deg_z g_i)\le d_i\le d$. Set $N=2n+1$ and let $G_i$ be the unperturbed forms (4.4), homogenizing all input and output coordinates while leaving $t$ as a coefficient parameter. For the full Puiseux field $\mathcal K$, APS is equivalent to the existence of $z=(z_0,\ldots,z_N)\in\mathcal K^{N+1}$ with
--
--   $$z_0\ne0,\qquad\min_{0\le j\le N}\operatorname{val}_t z_j=0,\qquad G_i(z,t)=0\ (1\le i\le N),\qquad\operatorname{val}_t(z_{n+i}/z_0)>0\ (1\le i\le n+1).$$
--
--   The first coordinate need only be nonzero as a series. This companion theorem supplies the precise homogeneous witness characterization omitted from the base milestone list.
--
--   Differences from the source:
--   - encoding: indices 0 through N and minimum valuation zero → Fin (N+1), all orders nonnegative and one order zero; reason: this is exactly the minimum condition on a finite nonempty family, with zero-series order infinity
--   - encoding: the full reduced-map, line and homogenization setup → published ReducedMap, LineData and HomogenizingDegrees parameters; reason: standing section hypotheses are explicit; all equations are the unperturbed published homogenizations
--   - encoding: Puiseux field K → published Hahn-series ambient with IsPuiseux on every coordinate; reason: arbitrary positive ramification denominators remain allowed
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 4.7, p. 20

import Definitions.Def_APSCounting893_Main_Resultant

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Theorem 4.7: unperturbed equations, normalized homogeneous coordinates, and
positive valuations of the dehomogenized outputs. The coefficient parameter t is untouched. -/
theorem homogeneous_puiseux_iff (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ)
    (hdegrees : HomogenizingDegrees F.toRawMap D.c D.alpha degrees) :
    hasAPS F.F ↔
      ∃ z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient,
        (∀ j, IsPuiseux (z j)) ∧ z 0 ≠ 0 ∧
        (∀ j, 0 ≤ (z j).orderTop) ∧ (∃ j, (z j).orderTop = 0) ∧
        (∀ i, MvPolynomial.eval₂
          (MvPolynomial.eval₂Hom HahnSeries.C
            (fun v : Fin 4 => if v = 2 then HahnSeries.single (1 : ℚ) (1 : ℂ) else 0))
          z (homogenizedEquation F.toRawMap D.c D.alpha degrees i) = 0) ∧
        (∀ i : Fin (F.n + 1), 0 < (z (i.natAdd F.n).succ / z 0).orderTop) := by sorry

end APSCounting893.Main.Supplement
