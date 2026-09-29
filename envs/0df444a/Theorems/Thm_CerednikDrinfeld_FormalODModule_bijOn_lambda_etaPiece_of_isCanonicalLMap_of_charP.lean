-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP
-- name    : CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/c63616a2-81d7-56a0-83a0-e3da43a5d598
-- title:
--   λ identifies ηₙ with the Pi=V locus
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring of characteristic $p$, and $j\colon W(\mathbb F_{p^2})\to B$ a ring homomorphism, where `Zp2 p` denotes $W(\mathbb F_{p^2})$. Let $X$ be a formal $\mathcal O_D$-module over $B$: a two–dimensional commutative formal group law $F$ together with an action of $W(\mathbb F_{p^2})$ by endomorphisms and a uniformiser $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ a=\sigma(a)\circ\varpi$. For $i\in\mathbb N$, `gradedPiece j i` is the subgroup of the Cartier module $M=$ `CartierModule p X.F` of those $f$ with $[c]\cdot f=j([c])^{p^i}f$ for every Teichmüller lift $[c]$, $c\in\mathbb F_{p^2}$; assume `hc`, that `gradedPiece j 0` and `gradedPiece j 1` are complementary. Then $M$, with Cartier Frobenius, the integral Verschiebung $V$, the $W(B)$-linear operator $\Pi$ induced by $\varpi$, and the two graded pieces indexed by $\mathrm{Fin}\,2$, forms the graded Cartier module datum $D=$ `X.toGradedCartierModuleData j hc`. Let $L\colon D.M\to D.\mathrm{NMod}$ be an additive map which is a canonical $L$-map, i.e. a Cartier $L$-map admitting a lift to a special graded Cartier module datum over a $p$-torsion-free ring surjecting onto $B$, compatibly with base change. Fix $n\in\mathrm{Fin}\,2$ and assume: every $z$ in the piece of index $n+1$ is of the form $\Pi m+Vm'$ with $m$ in the piece of index $n$ and $m'\in M$; and, for $m$ in the piece of index $n$, $\Pi m\in VM$ implies $m\in VM$. The conclusion is that the $W(B)$-linear map $\lambda\colon D.\mathrm{NMod}\to D.M$, induced on the quotient $\mathrm{NMod}$ by $(m,s)\mapsto \Pi m+V(s)$, is a bijection from the subgroup `etaPiece L _ n` — the intersection of $\eta(L)$ with the degree-$n$ part of $\mathrm{NMod}$, the hypothesis $L(Vx)=[(\Pi x,0)]$ being taken from the $L$-map property — onto the set $\{m\in M : m$ lies in the piece of index $n+1$ and $\Pi m=Vm\}$.
--
--   This is the step, in the Čerednik–Drinfeld theory of special formal $\mathcal O_D$-modules, at which the $\lambda$-map identifies the graded piece $\eta_n$ of the $N$-module with the locus where $\Pi$ and $V$ agree in the next graded piece, under the elementwise form of bijectivity of $\Pi$ modulo $V$; it corresponds to Boutot–Carayol II (4.6)–(4.8). The base is an arbitrary ring of characteristic $p$ so that the result applies to geometric fibres, and it is used in the fibrewise computations of tangent and Lie data over algebraically closed fields and in the construction of bijections on $\eta$-pieces for rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP.lean

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

theorem CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (n : Fin 2)
    (hsurj : ∀ z ∈ X.gradedPiece j ((n + 1 : Fin 2) : ℕ), ∃ m ∈ X.gradedPiece j (n : ℕ),
      ∃ m' : MvFormalGroup.CartierModule p X.F, z = MvFormalGroup.CartierModule.endAct X.varpiEnd m + MvFormalGroup.CartierModule.verschiebungInt m')
    (hinj : ∀ m ∈ X.gradedPiece j (n : ℕ),
      (∃ g : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m) →
        ∃ g' : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g' = m) :
    Set.BijOn (X.toGradedCartierModuleData j hc).lambda
      ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung n : Set _)
      {m : MvFormalGroup.CartierModule p X.F | m ∈ X.gradedPiece j ((n + 1 : Fin 2) : ℕ) ∧ MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m} := by sorry
