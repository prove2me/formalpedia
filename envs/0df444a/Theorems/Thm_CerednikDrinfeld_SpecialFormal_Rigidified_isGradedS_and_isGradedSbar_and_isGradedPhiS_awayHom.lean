-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/bbd4e6b3-e797-5adb-974c-a404b018c367
-- title:
--   Graded pieces split over basic opens of a p-nilpotent base
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to O$ (here $\mathrm{Zp2}\,p = W(\mathbb{F}_{p^2})$ is the Witt vectors of $\mathbb{F}_{p^2}$), a formal $O_D$-module $\Phi$ over $O/pO$, that is, a commutative two-dimensional formal group law over $O/pO$ together with an action of $W(\mathbb{F}_{p^2})$ and a uniformiser series $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi \circ [a] = [\sigma(a)]\circ \varpi$, a commutative ring $B$ with a ring homomorphism $\psi : O \to B$ such that $p$ is nilpotent in $B$, a rigidified object $t$ over $B$ (consisting of a formal $O_D$-module $t.X$ over $B$, an integer $n$, and a system of series $\rho$ over $B/pB$), and an element $g \in B$. Write $S = B_g$ for the localisation of $B$ at the powers of $g$ and $\mathrm{awayHom}\,g : B \to S$ for the canonical map. The conclusion is the conjunction of three statements, each asserting that two additive subgroups of a Cartier module are complementary (`IsCompl`): for the base change $t.XS$ of $t.X$ to $S$ with the induced map $jS$, for the reduction $t.\overline{X}S$ of $t.\overline{X}$ to $S/pS$ with $j\overline{S}$, and for $\overline{\Phi}S = (\Phi \otimes_{O/pO} B/pB)\otimes_{B/pB} S/pS$ with $j\Phi S$, the graded pieces in degrees $0$ and $1$ — the sets of Cartier-module elements $f$ with $[\,\omega(c)\,]\cdot f = j(\omega(c))^{p^n} f$ for all $c \in \mathbb{F}_{p^2}$, where $\omega$ denotes the Teichmüller lift and $n = 0,1$ — form a pair of complements.
--
--   This is the statement that, over a base in which $p$ is nilpotent, the Cartier module of each of the three formal $O_D$-modules attached to a rigidified object decomposes as the direct sum of its two eigencomponents for the Teichmüller action, simultaneously for every basic open $\operatorname{Spec} B_g$ of the base. It supplies the gradings needed to build $\xi$- and $\eta$-sections in the Čerednik–Drinfeld uniformisation machinery, and is cited by the constructions of $\eta$-sections with prescribed tangent behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (g : B) :
    t.IsGradedS ι ψ (Rigidified.awayHom g) ∧ t.IsGradedSbar ι ψ (Rigidified.awayHom g) ∧
      Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom g) := by sorry
