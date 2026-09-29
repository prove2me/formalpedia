-- Prove2me | Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one
-- name    : CerednikDrinfeld.CosetGraph.exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/cedf6cff-9db6-5d77-a138-4a5a40aeca8a
-- title:
--   Finite-index subgroup of away units with torsion-free image
-- statement:
--   Fix rationals $a,b$ and a prime $q'$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is definite and ramified exactly at $q'$ in the sense of `IsDefiniteRamifiedExactlyAt`: $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible precisely when $q'\in v$. Fix $N\neq 0$ and a $\mathbb{Z}$-submodule $R$ which is an Eichler order of level $N$, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_i$ with $[\Lambda_1:R]=N$. Fix a prime $r\neq q'$ with $r\nmid N$, a height-one prime $v$ containing $r$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $r$ a nonunit of $A$, and a discrete valuation ring $R_0$ that is an $\mathcal{O}$-algebra with fraction field `ratClosure A` (the closure of the prime subfield in the completion of $A$) whose image is exactly the elements of valuation $\le 1$. Fix an injective $\mathbb{Q}$-algebra map $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathrm{ratClosure}\,A)$, the induced $\rho:\mathbb{H}[\mathbb{Q},a,b]^\times\to \mathrm{PGL}_2$, and any action of $\mathbb{H}[\mathbb{Q},a,b]^\times$ on the vertices of the Bruhat–Tits tree of $(R_0,\mathrm{ratClosure}\,A)$. Then there is a subgroup $\Gamma''$ of $\mathrm{awayUnits}(R,v)\sqcap\mathrm{typePreserving}$ (the latter: elements preserving the mod-$2$ graph distance from the standard vertex) of nonzero relative index in it, such that every finite-order element of $\rho(\Gamma'')$ is trivial.
--
--   This supplies the virtual torsion-freeness input needed to realise the quotient of the Bruhat–Tits tree by the type-preserving $r$-away unit group of an Eichler order as a Mumford curve; it is used by the construction of the Čerednik–Drinfeld curve over the invariant field and by the associated descent statements. The classical source of the torsion statement is the theory of discrete subgroups acting on trees, where finite stabilisers force torsion elements of a suitable finite-index subgroup to be trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_CosetGraph_exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion MatrixGroups
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld ValuationSubring

theorem CerednikDrinfeld.CosetGraph.exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ratClosure A)] [IsFractionRing R₀ ↥(ratClosure A)]
    (hR₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔
      Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) (hι : Function.Injective ι)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, ↥(ratClosure A)))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x))
    [MulAction (ℍ[ℚ, a, b])ˣ (LT.LatticeTree.Vertex R₀ ↥(ratClosure A))] :
    ∃ Γ'' : Subgroup (ℍ[ℚ, a, b])ˣ,
      Γ'' ≤ CosetGraph.awayUnits R v ⊓ Mumford.typePreserving (ℍ[ℚ, a, b])ˣ (BruhatTits.tree R₀ ↥(ratClosure A))
          (LT.LatticeTree.stdVertex R₀ ↥(ratClosure A)) ∧
      Γ''.relIndex (CosetGraph.awayUnits R v ⊓ Mumford.typePreserving (ℍ[ℚ, a, b])ˣ (BruhatTits.tree R₀ ↥(ratClosure A))
          (LT.LatticeTree.stdVertex R₀ ↥(ratClosure A))) ≠ 0 ∧
      ∀ g ∈ Γ''.map ρ, IsOfFinOrder g → g = 1 := by sorry
