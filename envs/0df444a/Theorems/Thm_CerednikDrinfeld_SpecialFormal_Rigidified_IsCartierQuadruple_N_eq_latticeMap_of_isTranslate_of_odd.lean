-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_eq_latticeMap_of_isTranslate_of_odd
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.N_eq_latticeMap_of_isTranslate_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/6cd71038-56c2-5919-92d3-f2f10abe89e1
-- title:
--   Odd isogeny-translate lattices in a Čerednik–Drinfeld Cartier quadruple
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : W(\mathbb F_{p^2}) \to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ over $W(k)/pW(k)$ which is special for the induced map $\bar\iota$ to $W(k)/pW(k)$ and satisfies `HasHeight 4`, i.e. the kernel of multiplication by $p$ is finite projective of degree $p^4$ over every field quotient. Assume the graded pieces of index $0$ and $1$ of the Cartier module of $\Phi$ for $\bar\iota$ are complementary (`hcΦ`), write $D_\Phi$ for the resulting graded Cartier module data, and let $r_\Phi : \mathbb Z_p^2 \to D_\Phi.\mathrm{NMod}$ be an additive map which, for every canonical $L$-map $L$, maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ eta piece of $L$. Let $B$ be a Noetherian commutative $\mathbb Z_p$-algebra with $p$ nilpotent, and $\psi : W(k) \to B$ a ring homomorphism. Let $E$ be an injective ring homomorphism from the centraliser of $\{\Phi.\mathrm{actEnd}\,a\} \cup \{\Phi.\mathrm{varpiEnd}\}$ into $M_2(\mathbb Q_p)$ such that $p^m E(e)$ is integral for every $e$, and such that for every $e$, every integral $A$ with $p^m E(e) = A$, and every additive endomorphism $N_e$ of $D_\Phi.\mathrm{NMod}$ induced on classes $\mathrm{nMk}$ by the action of $e$ on Cartier modules, one has $p^m N_e(r_\Phi w) = r_\Phi(Aw)$ for all $w \in \mathbb Z_p^2$. Let $e$ lie in that centraliser, with kernel of its power series of degree $p^{2m'}$, and let $g \in \mathrm{GL}_2(\mathbb Q_p)$ have underlying matrix $E(e)$. Let $t$, $t'$ be rigidified objects over $B$, admissible for $(\iota,\psi)$ and for $(\iota, \psi \circ \sigma^{m'})$ respectively, with $t'$ the $e$-translate of $t$ in the sense `IsTranslate` at parameters $0$ and $m'$ (so $t'.X = t.X$, and for some $c$ the rigidification $t'.\rho$ precomposed with the $m'$-th Frobenius series agrees, after applying $[p^{c+t.n}]$ resp. $[p^{c+t'.n}]$, with $t.\rho$ composed with the reduction of $e$). Let $Q$, $Q'$ be Drinfeld data over $B$ for the uniformiser $p \in \mathbb Z_p$ in $\mathbb Q_p$ forming Cartier quadruples with $t$ over $\psi$ and with $t'$ over $\psi \circ \sigma^{m'}$. Assume $m' = 2j+1$ is odd and take units $c_0 = p^{j+1}$, $c_1 = p^{j}$ of $\mathbb Q_p$. Then for every $x \in \operatorname{Spec} B$ the lattices of $Q'$ are the parity-exchanged scalar translates $Q'.N_0(x) = c_0\,g^{-1}\,Q.N_1(x)$ and $Q'.N_1(x) = c_1\,g^{-1}\,Q.N_0(x)$, the translates being images under the matrix $\mathrm{scalarGL}(c_i)\,g^{-1}$ acting on $\mathbb Q_p^2$ by `mulVec`.
--
--   This is the odd-parity half of the computation, in Boutot–Carayol II (9.1)–(9.3), of the effect of an isogeny-translate on the lattice chain attached to a special formal $\mathcal O_D$-module: when $m'$ is odd the twist of the structure map by $\sigma^{m'}$ interchanges the two graded pieces, so the lattices $N_0$, $N_1$ are exchanged and rescaled by $p^{j+1}$ and $p^{j}$. It is used, together with its even counterpart, by [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isTranslateEven_or_isTranslateOdd_of_isTranslate`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isTranslateEven_or_isTranslateOdd_of_isTranslate) in the construction of the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_eq_latticeMap_of_isTranslate_of_odd.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.N_eq_latticeMap_of_isTranslate_of_odd
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]) (m : ℕ)
    (hEinj : Function.Injective E)
    (hEord : ∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEcompat : (∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) →
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p ^ m • Ne (rΦ w) = rΦ (A.mulVec w)))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = E e)
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')))
    (htr : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t t')
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) Q')
    (j : ℕ) (hm' : m' = 2 * j + 1) (c₀ c₁ : ℚ_[p]ˣ)
    (hc₀ : (c₀ : ℚ_[p]) = (p : ℚ_[p]) ^ (j + 1)) (hc₁ : (c₁ : ℚ_[p]) = (p : ℚ_[p]) ^ j) :
    ∀ x : PrimeSpectrum B,
      Q'.N₀ x = latticeMap (scalarGL c₀ * g⁻¹) (Q.N₁ x) ∧ Q'.N₁ x = latticeMap (scalarGL c₁ * g⁻¹) (Q.N₀ x) := by sorry
