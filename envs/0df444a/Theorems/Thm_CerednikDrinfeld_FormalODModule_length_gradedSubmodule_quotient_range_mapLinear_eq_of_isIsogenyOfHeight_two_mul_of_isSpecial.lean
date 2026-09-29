-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
-- name    : CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/e7c62242-76c6-5a73-af48-46686a036f26
-- title:
--   Isogeny of height 2h: colength h on each graded piece
-- statement:
--   Let $p$ be a prime and $K$ a perfect field of characteristic $p$, and let $j \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to K$ be a ring homomorphism. Let $Y, Z$ be formal $\mathcal{O}_D$-modules over $K$, that is, commutative two-dimensional formal group laws equipped with an action of $W(\mathbb{F}_{p^2})$ by endomorphisms of the law and a series $\varpi$ with $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\mathrm{Frob}\,a] \circ \varpi$. Assume both are special for $j$ (the subspaces $\mathrm{Lie}_0$ and $\mathrm{Lie}_1$ of the Lie module, cut out by the eigenvalue conditions $[a]_* = j(a)$ and $[a]_* = j(\mathrm{Frob}\,a)$, are complementary and invertible), that both have height $4$ (the kernel algebra of $[p]$ is finite, projective, and of rank $p^4$ at every field point), and that in each Cartier module the graded pieces for $n=0$ and $n=1$ — the subgroups on which the Teichmüller endomorphism $[\tau(c)]$ acts as homothety by $j(\tau(c))^{p^n}$ for all $c \in \mathbb{F}_{p^2}$ — are complementary. Let $\rho$ be a $2$-tuple of formal power series in two variables which is a homomorphism of formal $\mathcal{O}_D$-modules from $Y$ to $Z$ (a law homomorphism commuting with the $W(\mathbb{F}_{p^2})$-action and with $\varpi$) whose kernel algebra is finite, projective and of rank $p^{2h}$ at every field point, and let $i \in \{0,1\}$. Then the induced $W(K)$-linear map $\rho_*$ on Cartier modules is injective, carries the $i$-th graded submodule of $Y$ into the $i$-th graded submodule of $Z$, and the quotient of the $i$-th graded submodule of $Z$ by the preimage, under its inclusion, of the image $\rho_*(\text{$i$-th graded submodule of } Y)$ has length $h$ over $W(K)$.
--
--   This is the graded refinement of the colength computation for isogenies of special formal $\mathcal{O}_D$-modules in the Čerednik–Drinfeld theory: total colength $2h$ on the Cartier module is balanced equally between the two eigenpieces of the $W(\mathbb{F}_{p^2})$-action. It is the numerical input for the determinant identities used in the analysis of rigidified special formal modules and of the fibres over the Drinfeld upper half plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (j : Zp2 p →+* K) (Y Z : FormalODModule p K) (hY : Y.IsSpecial j) (hZ : Z.IsSpecial j)
    (hY4 : Y.HasHeight 4) (hZ4 : Z.HasHeight 4)
    (hcY : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (hcZ : IsCompl (Z.gradedPiece j 0) (Z.gradedPiece j 1))
    (ρ : SpecialFormal.Series K) (h : ℕ) (hρ : FormalODModule.IsIsogenyOfHeight Y Z ρ (2 * h))
    (i : Fin 2) :
    Function.Injective (MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom) ∧
    Submodule.map (MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom) (Y.gradedSubmodule j (i : ℕ)) ≤
      Z.gradedSubmodule j (i : ℕ) ∧
    Module.length (WittVector p K)
        (↥(Z.gradedSubmodule j (i : ℕ)) ⧸
          Submodule.comap (Z.gradedSubmodule j (i : ℕ)).subtype
            (Submodule.map (MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom)
              (Y.gradedSubmodule j (i : ℕ)))) = h := by sorry
