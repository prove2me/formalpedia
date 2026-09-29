-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/1dc8252d-bd94-5737-83eb-3db77cbf85d9
-- title:
--   Nonvanishing of a+b in K for a principal root
-- statement:
--   Fix natural numbers $g,d,n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero and $\prod_i \delta_i = d$, a commutative ring $S$ in which the image of $d$ is a unit, and a term $u$ of `PolarisedAbelianScheme g d n S`: a scheme $A$ with a morphism $u.f : A \to \operatorname{Spec} S$, a commutative relative group law $u.L$ on the functor of sections of $u.f$, an `AbelianSchemePropertyBundle` for $u.f$, all fibres of topological Krull dimension $g$, sections $P_i$ ($i \in \mathrm{Fin}(2g)$) that are $n$-torsion and that parametrise the $n$-torsion freely at every algebraically closed geometric point, and an invertible module $u.\mathrm{pol}$ on $A$ which is a closed immersion by sections over $S$ and has geometric fibre $H^0$-rank $d$. Let $K$ be an algebraically closed field and $t : \operatorname{Spec} K \to \operatorname{Spec} S$; write $p_1 =$ `pullback.fst u.f t` and $p_2 =$ `pullback.snd u.f t` for the two projections of $A \times_{\operatorname{Spec} S} \operatorname{Spec} K$. Assume given a relative group law $L'$ on the sections of $p_2$ which is compatible with $u.L$ along $p_1$: for every scheme $T$, every $t' : T \to \operatorname{Spec} K$ and all sections $P,Q$ of $p_2$ over $t'$, the morphism underlying $L'.\mathrm{mul}\,t'\,P\,Q$ followed by $p_1$ agrees with the morphism underlying the $u.L$-product, over $t' \circ t$ composed with $t$, of $P$ and $Q$ pushed forward by $p_1$. Assume further an invertible module $\mathcal{L}_0$ on the fibre product, natural numbers $a,b$ with $1 \le a+b$, that $(p_2, L', \mathcal{L}_0)$ satisfies `KernelTrivial`, i.e. for every commutative ring $R$, every $t'' : \operatorname{Spec} R \to \operatorname{Spec} K$ and every section $x$ of $p_2$ over $t''$, local isomorphy over the base of the pullback along `sliceAt` of the Mumford bundle of $\mathcal{L}_0$ to the unit object forces $x = L'.\mathrm{one}$; and that the pullback of $u.\mathrm{pol}$ along $p_1$ is locally isomorphic on the base $\operatorname{Spec} K$ (each point has an open neighbourhood $U$ over whose preimage the two restrictions are isomorphic) to $\mathcal{L}_0^{\otimes a} \otimes (\nu^{*}\mathcal{L}_0)^{\otimes b}$, where $\nu$ is the morphism underlying the $L'$-inverse of the identity section and tensor powers are the iterated `tpow`. Finally assume `RootedSymmetricOfType δ S u`, i.e. $u.\mathrm{pol}$ is locally isomorphic on the base to its pullback along the $u.L$-negation, together with the predicates `IsOfType δ u` and `HasPrincipalRoot u`, and assume $0 < g$. The conclusion is that $a+b$ is nonzero in $K$, i.e. the characteristic of $K$ does not divide $a+b$.
--
--   The statement records that the exponent $a+b$ occurring in a principal root of the polarisation of a polarised abelian scheme with $d$ invertible is prime to the residue characteristic at each geometric point with fibres of positive dimension; the mechanism is the identification of the kernel of $\mathcal{L}_0^{\otimes a} \otimes (\nu^*\mathcal{L}_0)^{\otimes b}$ with the $(a+b)$-torsion, which would acquire infinitesimal points over $K[\varepsilon]$ in the divisible case. It is used in the analysis of theta points, by [`AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_isAlgClosed`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators MonoidalCategory

theorem AlgebraicGeometry.PolarisedAbelianScheme.natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (hd : IsUnit ((d : ℕ) : S))
    (u : PolarisedAbelianScheme g d n S)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))

    (L' : RelativeGroupLaw K (pullback.snd u.f t))
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' (pullback.snd u.f t)),
      (L'.mul t' P Q).1 ≫ pullback.fst u.f t =
        (u.L.mul (t' ≫ t)
          ⟨P.1 ≫ pullback.fst u.f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst u.f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (𝓛₀ : (pullback u.f t).Modules) (a b : ℕ) (hab : 1 ≤ a + b) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hker : Polarisation.KernelTrivial (pullback.snd u.f t) L' 𝓛₀)
    (hroot : Polarisation.LocIsoOnBase (pullback.snd u.f t)
      ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol)
      (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor (pullback.snd u.f t) L')).obj 𝓛₀) b))
    (hu : PolarisedAbelianScheme.RootedSymmetricOfType δ S u) (hg : 0 < g) :
    ((a + b : ℕ) : K) ≠ 0 := by sorry
