-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/c1117ad3-ddcc-5152-8560-b02730dd7d56
-- title:
--   Tangent classes of η(L) span both Lie pieces over 𝔽̄ₚ
-- statement:
--   Let $p$ be a prime, let $K$ be an algebraically closed field of characteristic $p$, let $j\colon W(\mathbb F_{p^2}) \to K$ be a ring homomorphism, and let $X$ be a formal $\mathcal O_D$-module over $K$ in the sense of `FormalODModule`: a $2$-dimensional commutative formal group law $F$ over $K$ together with an action of $W(\mathbb F_{p^2})$ by endomorphisms of $F$ and an endomorphism $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$. Assume $X$ is special for $j$, i.e. the submodules $\operatorname{Lie}_0 = \bigcap_a \ker(\mathrm{lieAct}(a) - j(a))$ and $\operatorname{Lie}_1 = \bigcap_a \ker(\mathrm{lieAct}(a) - j(\sigma a))$ of $\operatorname{Lie} X$ are complementary and each invertible; assume $X$ has height $4$, i.e. $[p]$ has kernel of degree $p^4$; and assume the two graded pieces of the Cartier module $M =$ `CartierModule p X.F` — where the $n$th piece consists of those $f$ with $[\,\tau(c)\,]_*f = j(\tau(c))^{p^n} f$ for all $c \in \mathbb F_{p^2}$, $\tau$ the Teichmüller lift — are complementary additive subgroups (hypothesis `hc`), which makes $M$ into graded Cartier module data $D$ with $F$-operator the Cartier Frobenius, $V$ the integral Verschiebung and $\varpi$ acting $\sigma$-semilinearly. Let $L\colon M \to N(M) = (M \times \Sigma)/\mathrm{nRel}$ be an additive map which is a canonical $L$-map, i.e. a Cartier $L$-map (so in particular $L(Vx) = [(\varpi x, 0)]$) that is moreover induced by base change along a surjection onto $K$ from a ring without $p$-torsion carrying special graded Cartier module data. Then for each $i = 0, 1$ the piece $\operatorname{Lie}_i$ is contained in the $K$-span of the set of tangent vectors $\operatorname{tangent}(a)$, for $a \in M$ such that some $z$ in the $i$th graded piece $\eta(L)_i = \eta(L) \cap N(M)_i$ satisfies $\mathrm{toLieQuot}(z) = a \bmod VM$; here $\operatorname{tangent}$ reads off the coefficients of the linear term in each of the two coordinates. Equivalently, the $K$-linear extension of $u(L)\colon \eta(L)_i \to M/VM$ has image spanning $\operatorname{Lie}_i$ for both $i$.
--
--   This is the surjectivity half of the comparison between the $\varphi_L$-invariants $\eta(L)$ of a special formal $\mathcal O_D$-module of height $4$ and its Lie algebra, as in Boutot–Carayol's treatment of the Čerednik–Drinfeld uniformisation, following Drinfeld. It is used in the proof that the map on stalks induced by the rigidified special formal module is surjective, via the tangent/germ description over Witt vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K] [CharP K p] (j : Zp2 p →+* K)
    (X : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    X.lieZero j ≤ Submodule.span K (MvFormalGroup.CartierModule.tangent ''
        {a : MvFormalGroup.CartierModule p X.F |
          ∃ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0,
            (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ a}) ∧
    X.lieOne j ≤ Submodule.span K (MvFormalGroup.CartierModule.tangent ''
        {a : MvFormalGroup.CartierModule p X.F |
          ∃ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1,
            (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ a}) := by sorry
