-- Prove2me | Theorems.Thm_AlgebraicGeometry_subsingleton_fppfH1_Gm_specZ
-- name    : AlgebraicGeometry.subsingleton_fppfH1_Gm_specZ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/dd214ba7-118b-5123-92db-b5b344cc5a1d
-- title:
--   Vanishing of H¹_{fppf}(Specℤ,G_m)
-- statement:
--   The assertion is a closed one: it has no variables and no hypotheses. Let $\mathbb{G}_m$ denote the multiplicative group scheme viewed as a presheaf of commutative groups on schemes in universe $0$; transporting it along the equivalence between commutative groups and additive commutative groups gives the fppf sheaf `FppfKummerSES.GmAbelianSheaf` of $\mathrm{AddCommGrpCat}.\{0\}$-valued sheaves for `Scheme.fppfTopology`, and applying the universe-lifting functor `AddCommGrpCat.uliftFunctor` objectwise (via `sheafCompose`) gives [`FppfKummerSES.GmAbelianSheafLifted`](def/AlgebraicGeometry_FppfKummerProp17.html#L387), an object of the abelian category of $\mathrm{AddCommGrpCat}.\{1\}$-valued sheaves on the big fppf site of $\mathrm{Scheme}.\{0\}$. The theorem states that the type [`FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted 1`](def/AlgebraicGeometry_FppfCohomologyLES.html#L175), that is the degree-$1$ sheaf-cohomology group `Sheaf.H 1` of this sheaf — the $\mathrm{Ext}$-group in degree $1$ from the constant sheaf with value $\mathrm{ULift}\ \mathbb{Z}$ to `GmAbelianSheafLifted` — is a subsingleton: it has at most one element. Since this group contains $0$, it is the trivial group. As $\operatorname{Spec}\mathbb{Z}$ is terminal among schemes, this is the vanishing of $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z},\mathbb{G}_m)$.
--
--   This is fppf Hilbert 90 over $\mathbb{Z}$ in the form $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z},\mathbb{G}_m)\cong\operatorname{Pic}(\operatorname{Spec}\mathbb{Z})=0$, the vanishing of the ideal class group of $\mathbb{Z}$ read cohomologically. It feeds the computation of the order of this group and, through the Kummer sequence for $\mu_p$ on the fppf site, the finiteness of $H^1_{\mathrm{fppf}}$ of $\mu_p$ over $\operatorname{Spec}\mathbb{Z}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_subsingleton_fppfH1_Gm_specZ.lean

import Definitions.Def_AlgebraicGeometry_FppfKummerProp17

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Abelian Limits AlgebraicGeometry

theorem AlgebraicGeometry.subsingleton_fppfH1_Gm_specZ :
    Subsingleton (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) := by sorry
