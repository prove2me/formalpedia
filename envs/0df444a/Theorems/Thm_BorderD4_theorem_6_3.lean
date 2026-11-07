-- Prove2me | Theorems.Thm_BorderD4_theorem_6_3
-- name    : BorderD4.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:04.013028+00:00
-- url     : https://prove2.me/theorems/6c9fb635-e4d7-458a-8ba5-c0634e8d13fb
-- title:
--   Theorem 6.3 (Abhyankar–Jung): $W(\varepsilon^e,u,z)$ splits when $\mathrm{Disc}_z W$ is an $\varepsilon$-unit
-- statement:
--   Let $F$ be algebraically closed of characteristic zero, $u$ a tuple of variables, and $W\in F[[\varepsilon,u]][z]$ monic of positive degree $d$. If $\mathrm{Disc}_z(W)$ is an $\varepsilon$-unit, then there are a positive integer $e$ and $r_1,\dots,r_d\in F[[\varepsilon,u]]$ with
--   $$W(\varepsilon^e,u,z)=\prod_{i=1}^d(z-r_i).$$
--   It replaces the implicit function theorem in the border setting, where a dependent coordinate may ramify at $\varepsilon=0$.
--
--   Differences from the source:
--   - encoding: the tuple $u$ → an arbitrary finite index type; reason: any such type is a tuple up to renaming
--   - encoding: $\mathrm{Disc}_z$ of p.42 → Mathlib's `Polynomial.discr`; reason: for monic $W$ they agree up to a sign, which does not change being an $\varepsilon$-unit
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.3, p.49; Theorem A.2, pp.89–90

import Mathlib
import Definitions.Def_BorderD4_IsEpsUnit
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Theorem 6.3 (= Theorem A.2), Abhyankar–Jung: if `W ∈ F[[ε, u]][z]` is monic of positive degree `d` and `Disc_z(W)`
is an ε-unit, then there are a positive integer `e` and `r_1, …, r_d ∈ F[[ε, u]]` with
`W(ε^e, u, z) = ∏_{i=1}^d (z − r_i)`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.3, p.49; Theorem A.2, pp.89–90.

**Formalization Note** `F` is algebraically closed of characteristic `0` (p.49). `Polynomial.discr` is Mathlib's
discriminant. For monic `W` it equals the page's `Disc_z` up to a sign, which does not change being an ε-unit. The
substitution `ε ↦ ε^e` acts on coefficients through `PowerSeries.expand`. -/
theorem theorem_6_3 {F τ : Type*} [Field F] [IsAlgClosed F] [CharZero F] [Fintype τ]
    (W : Polynomial (EpsSeries F τ)) (hW : W.Monic) (hd : 0 < W.natDegree)
    (hdisc : IsEpsUnit W.discr) :
    ∃ (e : ℕ) (he : e ≠ 0) (r : Fin W.natDegree → EpsSeries F τ),
      W.map ((PowerSeries.expand e he : EpsSeries F τ →ₐ[MvPowerSeries τ F] EpsSeries F τ) :
          EpsSeries F τ →+* EpsSeries F τ) =
        ∏ i, (Polynomial.X - Polynomial.C (r i)) := by sorry

end BorderD4
