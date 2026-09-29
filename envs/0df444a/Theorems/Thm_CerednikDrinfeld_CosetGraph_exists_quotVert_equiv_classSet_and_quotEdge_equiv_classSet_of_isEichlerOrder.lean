-- Prove2me | Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_quotVert_equiv_classSet_and_quotEdge_equiv_classSet_of_isEichlerOrder
-- name    : CerednikDrinfeld.CosetGraph.exists_quotVert_equiv_classSet_and_quotEdge_equiv_classSet_of_isEichlerOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/a21bfe10-d2cb-58af-8420-421bf19fda4e
-- title:
--   Coset graph quotient at r is the class-set degeneracy datum
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $q'\ge 5$ be a prime such that $a<0$, $b<0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q'\in v$; let $N\ge 1$ be squarefree, and let $\Lambda, R$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$ with $\Lambda$ a maximal order, $R$ an Eichler order of level $N$ (an intersection of two maximal orders, of relative index $N$ in the first), and $R\le\Lambda$. Let $r$ be a prime with $r\ne q'$ and $r\nmid N$, let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ containing $r$, and let $n$ be a unit of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ in the prime Hecke set of $R$ at $r$, that is: $n$ lies in the finite adelic box of $R$, so does $r\cdot n^{-1}$, while neither $n^{-1}$ nor $r^{-1}n$ does. Assume that `meetOrder R n` $=R\cap nRn^{-1}$ is an Eichler order of level $Nr$, that conjugation by $n$ preserves it, and that the shift $x\mapsto[\,x\,n\,]$ is an involution of the class set $\mathrm{ClassSet}$ of its finite idelic stabiliser; both class sets occurring are assumed finite. Then there exist bijections $e_V$ from the orbit set of `ProjAwayUnits R v` (the units of $\mathbb{H}[\mathbb{Q},a,b]$ lying locally in the box-unit subgroup at every place $w\ne v$, modulo the kernel of the action) acting on $\mathrm{Vert}=(\mathbb{H}[\mathbb{Q},a,b]\otimes\mathbb{Q}_v)^{\times}/\mathrm{level}(R,v)$ onto $\mathrm{ClassSet}$ of the finite idelic stabiliser of $R$, and $e_E$ from the orbit set of darts of the coset graph `graph R v` built from the local component $n_v$ of $n$ onto $\mathrm{ClassSet}$ of the stabiliser of `meetOrder R n`, such that: for every finite idelic unit $x$ whose components at all $w\ne v$ are $1$, $e_V$ sends the orbit of the class of $x_v$ to the double coset of $x$; for every dart $d$ and every such $x$ with $d.\mathrm{fst}=[x_v]$ and $d.\mathrm{snd}=[x_v n_v]$, $e_E$ sends the orbit of $d$ to the double coset of $x$; and $e_V$, $e_E$ identify the quotient degeneracy datum (dart origin, dart terminus, and the order of the dart stabiliser as a positive natural number) with the class-set degeneracy datum of $(R,n)$, whose legs are the forgetful map of class sets and the shift by $n$, and whose weight is `unitWeight` of the conjugate of `meetOrder R n` by a representative.
--
--   This is the arithmetic–combinatorial dictionary underlying the Čerednik–Drinfeld description of the special fibre at $r$: the quotient of the coset (Bruhat–Tits) graph at $v\mid r$ by the $r$-units of the Eichler order is identified, as a two-legged datum with weights, with the class-set (Brandt) graph of the definite quaternion algebra of discriminant $q'$ with Eichler levels $N$ and $Nr$. It is the source of the Mumford-side frame results on stabilisers, finiteness of the quotient and the shift-forget description of the legs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_CosetGraph_exists_quotVert_equiv_classSet_and_quotEdge_equiv_classSet_of_isEichlerOrder.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.exists_quotVert_equiv_classSet_and_quotEdge_equiv_classSet_of_isEichlerOrder
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hq5 : 5 ≤ q') (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (N : ℕ) [NeZero N] (hN : Squarefree N) (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (r : ℕ) [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R r)
    (hS : IsEichlerOrder (meetOrder R n) (N * r))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))] :
    ∃ (eV : Mumford.QuotVert (CosetGraph.ProjAwayUnits R v) (CosetGraph.Vert R v) ≃
          ClassSet (Submodule.finiteIdeleStabilizer R))
      (eE : Mumford.QuotEdge (CosetGraph.ProjAwayUnits R v)
          (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)) ≃
          ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n))),
      (∀ x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) →
        eV (Quotient.mk (MulAction.orbitRel (CosetGraph.ProjAwayUnits R v) (CosetGraph.Vert R v))
          ((QuotientGroup.mk (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom x) :
            CosetGraph.Vert R v))) =
          ClassSet.mk (Submodule.finiteIdeleStabilizer R) x) ∧
      (∀ (d : (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart)
        (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) →
        d.fst = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom x : (CosetGraph.Loc a b v)ˣ) :
          CosetGraph.Vert R v) →
        d.snd = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom x *
          Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n : (CosetGraph.Loc a b v)ˣ) :
            CosetGraph.Vert R v) →
        eE (Quotient.mk (MulAction.orbitRel (CosetGraph.ProjAwayUnits R v)
          (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart) d) =
          ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) x) ∧
      (∀ e, eV ((Mumford.quotientDegeneracyData (CosetGraph.ProjAwayUnits R v)
          (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n))).a e) =
        (classSetDegeneracyData R n).a (eE e)) ∧
      (∀ e, eV ((Mumford.quotientDegeneracyData (CosetGraph.ProjAwayUnits R v)
          (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n))).b e) =
        (classSetDegeneracyData R n).b (eE e)) ∧
      (∀ e, (Mumford.quotientDegeneracyData (CosetGraph.ProjAwayUnits R v)
          (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n))).w e =
        (classSetDegeneracyData R n).w (eE e)) := by sorry
