-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_map_varpiLinear_eq_one_of_isSpecial_of_hasHeight
-- name    : CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_map_varpiLinear_eq_one_of_isSpecial_of_hasHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/5e53c3ba-41f9-56e8-8621-b2642b74cd7e
-- title:
--   Pi has colength one on each graded Cartier piece
-- statement:
--   Let $p$ be a prime and let $K$ be a perfect field of characteristic $p$, let $j : W(\mathbb{F}_{p^2}) \to K$ be a ring homomorphism (the source being the Witt vectors of the field with $p^2$ elements), and let $Y$ be a formal $\mathcal{O}_D$-module over $K$, that is, a commutative two-variable formal group law $Y.F$ together with an action of $W(\mathbb{F}_{p^2})$ by endomorphisms of the group law (unital, multiplicative and additive) and a further endomorphism $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\varphi(a)] \circ \varpi$ for the Witt Frobenius $\varphi$. Assume $Y$ is special for $j$, i.e. the two Lie pieces $Y.\mathrm{lieZero}\,j$ and $Y.\mathrm{lieOne}\,j$ are complementary and each is an invertible $K$-module, and that $Y$ has height $4$, i.e. the series $[p]$ has kernel of degree $p^4$. Fix $i \in \mathbb{Z}/2$. Write $M_n \subseteq \mathrm{CartierModule}\,p\,Y.F$ for the $W(K)$-submodule of those $f$ with $[\tau(c)]\cdot f = j(\tau(c))^{p^n} f$ for every $c \in \mathbb{F}_{p^2}$ (Teichmüller lifts $\tau$, homothety action on the right), and $\Pi$ for the $W(K)$-linear endomorphism of the Cartier module induced by $\varpi$. Then $\Pi(M_i) \subseteq M_{i+1}$, indices in $\mathbb{Z}/2$, and the quotient of $M_{i+1}$ by $\Pi(M_i)$ (formed as the quotient of $M_{i+1}$ by the pullback of $\Pi(M_i)$ along the inclusion of $M_{i+1}$) has length $1$ over $W(K)$.
--
--   This is the standard statement that, for a special formal $\mathcal{O}_D$-module of height $4$ over a perfect field, the uniformiser $\Pi$ of the quaternion order shifts the $\mathbb{Z}/2$-graded Cartier module by one degree and has colength exactly one in each degree; it is the local input to Drinfeld's description of such modules in terms of lattice chains. It is used in the rigidified setting to compute the determinant of the matrix expressing the $\Pi$- and $V$-structure on a homogeneous basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_map_varpiLinear_eq_one_of_isSpecial_of_hasHeight.lean

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

theorem CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_map_varpiLinear_eq_one_of_isSpecial_of_hasHeight
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (j : Zp2 p →+* K) (Y : FormalODModule p K) (hY : Y.IsSpecial j) (hY4 : Y.HasHeight 4)
    (i : Fin 2) :
    Submodule.map Y.varpiLinear (Y.gradedSubmodule j (i : ℕ)) ≤ Y.gradedSubmodule j ((i + 1 : Fin 2) : ℕ) ∧
    Module.length (WittVector p K)
        (↥(Y.gradedSubmodule j ((i + 1 : Fin 2) : ℕ)) ⧸
          Submodule.comap (Y.gradedSubmodule j ((i + 1 : Fin 2) : ℕ)).subtype
            (Submodule.map Y.varpiLinear (Y.gradedSubmodule j (i : ℕ)))) = 1 := by sorry
