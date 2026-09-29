-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/5d6b0789-9a4a-561d-8c7a-a32048ec452a
-- title:
--   Extending an invariant bijection to the critical graded pieces
-- statement:
--   Fix a prime $p$, an algebraically closed field $K$ of characteristic $p$ and a ring homomorphism $j \colon W(\mathbb{F}_{p^2}) \to K$, where $W(\mathbb{F}_{p^2})$ is realised as `Zp2 p`, the Witt vectors of `GaloisField p 2`. Let $X$ and $X'$ be formal $\mathcal{O}_D$-modules over $K$, i.e. two-dimensional commutative formal group laws $F$ equipped with an action of `Zp2 p` by endomorphisms and an endomorphism $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\mathrm{Frob}\, a] \circ \varpi$. Assume each is special for $j$ (its degree-zero and degree-one Lie parts are complementary and each invertible as a $K$-module) and has height $4$ (the kernel of $[p]$ has degree $p^4$). Let $i$ be a natural number that is critical for both $X$ and $X'$, meaning that for every $m$ in the $i$-th graded piece — the subgroup of the Cartier module of $F$ on which each Teichmüller lift $\tau(c)$, $c \in \mathbb{F}_{p^2}$, acts as multiplication by the Teichmüller lift of $j(\tau(c))^{p^i}$ — the element $\varpi m$ lies in the image of the Verschiebung. Let $\theta_0$ be a bijective additive map from the invariants of $X$ at $i$ (elements $m$ of the $i$-th graded piece with $\varpi m = V m$) to those of $X'$ at $i$. Then there is a $W(K)$-linear map $\Theta$ from the Cartier module of $X.F$ to that of $X'.F$ which maps the $i$-th graded piece of $X$ bijectively onto the $i$-th graded piece of $X'$ and agrees with $\theta_0$ on the invariants of $X$ at $i$.
--
--   This is the rigidity step in the Čerednik–Drinfeld theory of special formal $\mathcal{O}_D$-modules: an additive isomorphism between the $\varpi = V$ invariants at a critical index, which form a free $\mathbb{Z}_p$-module of rank $2$, propagates to a $W(K)$-linear isomorphism of the whole critical graded piece. It is used in the construction of bijections of Cartier modules attached to Cartier quadruples over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (X X' : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hX' : X'.IsSpecial j) (hX'4 : X'.HasHeight 4)
    (i : ℕ) (hi : FormalODModule.CritChart.IsCritical X j i) (hi' : FormalODModule.CritChart.IsCritical X' j i)
    (θ₀ : FormalODModule.CritChart.invariants X j i →+ FormalODModule.CritChart.invariants X' j i)
    (hθ₀ : Function.Bijective θ₀) :
    ∃ Θ : MvFormalGroup.CartierModule p X.F →ₗ[WittVector p K] MvFormalGroup.CartierModule p X'.F,
      Set.BijOn Θ (X.gradedPiece j i : Set (MvFormalGroup.CartierModule p X.F)) (X'.gradedPiece j i) ∧
      ∀ m : FormalODModule.CritChart.invariants X j i,
        Θ (m : MvFormalGroup.CartierModule p X.F) = ((θ₀ m : FormalODModule.CritChart.invariants X' j i) : MvFormalGroup.CartierModule p X'.F) := by sorry
