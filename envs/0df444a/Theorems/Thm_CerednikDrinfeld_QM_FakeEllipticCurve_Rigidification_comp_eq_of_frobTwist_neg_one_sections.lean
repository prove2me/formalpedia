-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_eq_of_frobTwist_neg_one_sections
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.comp_eq_of_frobTwist_neg_one_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/26315007-f3c4-572d-b6cb-efede657866f
-- title:
--   Verschiebung compares the rebased sections of a rigidification
-- statement:
--   Fix a prime $r$ and a natural number $N$. Let $\mathcal{O}$ be a characteristic-zero domain that is a discrete valuation ring, $\pi$ an irreducible element, $\mathcal{O}$ being $\pi$-adically complete with residue ring of cardinality $r$ and with $(r)=(\pi)$; let $Onr$ be a characteristic-zero $\mathcal{O}$-domain with an $\mathcal{O}$-algebra automorphism $Fr$, complete for the ideal $(\pi)$, with $(\pi)$ maximal, every element satisfying a monic polynomial over $\mathcal{O}$ modulo $\pi$, every monic polynomial over $Onr$ of positive degree having a root modulo $\pi$, and $Fr(x)\equiv x^{r} \pmod{\pi}$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$, write $k_0=Onr/(\pi)$, let $A_0$ be a fake elliptic curve of type $(\Lambda,N)$ over $k_0$ with a $k_0$-point $P_0$ (a section of $A_0.f$ over the identity), let $A_{0r}$ be a further such object with $\mathrm{pr}_A:A_{0r}.A\to A_0.A$ exhibiting $A_{0r}$ as the base change of $A_0$ along the residue map induced by $Fr^{-1}$ (cartesian, compatible with the relative group law, the $\Lambda$-action and the level structure), and let $F:A_0.A\to A_{0r}.A$, $V:A_{0r}.A\to A_0.A$ be morphisms over $\mathrm{Spec}\,k_0$ that are homomorphisms on points, commute with the $\Lambda$-action, carry points factoring through the level scheme to such points, and satisfy $V\circ F=[r]$, $F\circ V=[r]$; assume further that for every commutative ring $C$ of characteristic $r$ and every $x:\mathrm{Spec}\,C\to A_{0r}.A$ one has $x$ followed by $V$ equal to $\mathrm{Spec}$ of the $r$-power Frobenius of $C$ followed by $x$ followed by $\mathrm{pr}_A$. Let $B$ be a nontrivial $\mathcal{O}$-algebra in which the image of $\pi$ is nilpotent, $\psi:Onr\to B$ an $\mathcal{O}$-algebra map, $E$ a fake elliptic curve of type $(\Lambda,N)$ over $B$, and let $\rho$, $\rho^{-}$ be rigidifications of $E$ relative to $(r,\pi,A_0)$ along $\psi$ and along $\mathrm{frobTwist}\,Onr\,Fr\,(-1)\,\psi=\psi\circ Fr^{-1}$ respectively. Comparison data are given: $ub$ between the $E$-sides compatible with $gb$ and the structure maps; $gA':\rho^{-}.Ab.A\to A_{0r}.A$ exhibiting $\rho^{-}.Ab$ as the base change of $A_{0r}$ along the residue map of $\psi$, with $gA'$ followed by $\mathrm{pr}_A$ equal to $\rho^{-}.gA$; and $Fb:\rho.Ab.A\to\rho^{-}.Ab.A$, $Vb:\rho^{-}.Ab.A\to\rho.Ab.A$ over $B/(\pi)$ with $Fb$ followed by $gA'$ equal to $\rho.gA$ followed by $F$, and $Vb$ followed by $\rho.gA$ equal to $gA'$ followed by $V$. Finally let $Q$ and $Q^{-}$ be sections of $\rho.Ab.f$ and of $\rho^{-}.Ab.f$ over $B/(\pi)$ whose composites with $\rho.gA$, respectively $\rho^{-}.gA$, are $\mathrm{Spec}$ of the residue map of $\psi$, respectively of $\psi\circ Fr^{-1}$, followed by $P_0$. The conclusion is that $Q^{-}$ followed by $Vb$ equals $Q$.
--
--   This is the point-level compatibility between the Verschiebung-type comparison $Vb$ and the two tautological sections attached to a single $k_0$-point $P_0$ of the base fake elliptic curve, for a rigidification and its rebasing along the inverse Frobenius of the unramified base. It is used in the identification of the full level structure transported by such a pair of rigidifications, in the Čerednik–Drinfeld uniformisation chain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_eq_of_frobTwist_neg_one_sections.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.comp_eq_of_frobTwist_neg_one_sections
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})))) A₀.f)
    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr.symm : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f) (V : A₀r.A ⟶ A₀.A) (hV : V ≫ A₀.f = A₀r.f)
    (F_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
      mapPt F hF (A₀.L.mul t P Q) = A₀r.L.mul t (mapPt F hF P) (mapPt F hF Q))
    (V_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀r.f),
      mapPt V hV (A₀r.L.mul t P Q) = A₀.L.mul t (mapPt V hV P) (mapPt V hV Q))
    (F_act : ∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x) (V_act : ∀ x : ↥Λ, A₀r.act x ≫ V = V ≫ A₀.act x)
    (F_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev P → FactorsThrough A₀r.lev (mapPt F hF P))
    (V_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
      FactorsThrough A₀r.lev Q → FactorsThrough A₀.lev (mapPt V hV Q))
    (V_F : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      mapPt V hV (mapPt F hF P) = nsmulPt A₀.L t r P)
    (F_V : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
      mapPt F hF (mapPt V hV Q) = nsmulPt A₀r.L t r Q)
    (V_frob : ∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀r.A),
      x ≫ V = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x ≫ prA)
    (B : Type) [CommRing B] [Nontrivial B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ρp : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (-1) ψ) E)
    (ub : ρ.Eb.A ⟶ ρp.Eb.A) (hub : ub ≫ ρp.gb = ρ.gb) (hub' : ub ≫ ρp.Eb.f = ρ.Eb.f)
    (gA' : ρp.Ab.A ⟶ A₀r.A) (hgA' : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρp.Ab gA')
    (hgA'' : gA' ≫ prA = ρp.gA)
    (Fb : ρ.Ab.A ⟶ ρp.Ab.A) (hFb : Fb ≫ gA' = ρ.gA ≫ F) (hFb' : Fb ≫ ρp.Ab.f = ρ.Ab.f)
    (Vb : ρp.Ab.A ⟶ ρ.Ab.A) (hVb : Vb ≫ ρ.gA = gA' ≫ V) (hVb' : Vb ≫ ρ.Ab.f = ρp.Ab.f)

    (Q : Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})) ⟶ ρ.Ab.A) (hQ : Q ≫ ρ.Ab.f = 𝟙 _)
    (hQA : Q ≫ ρ.gA = Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) ≫ P₀.1)
    (Qp : Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})) ⟶ ρp.Ab.A) (hQp : Qp ≫ ρp.Ab.f = 𝟙 _)
    (hQpA : Qp ≫ ρp.gA = Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π (frobTwist Onr Fr (-1) ψ))) ≫ P₀.1) :
    Qp ≫ Vb = Q := by sorry
