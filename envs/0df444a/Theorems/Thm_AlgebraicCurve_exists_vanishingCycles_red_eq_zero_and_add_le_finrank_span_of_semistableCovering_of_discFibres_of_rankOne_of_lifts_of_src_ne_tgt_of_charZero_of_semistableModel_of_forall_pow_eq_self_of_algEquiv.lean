-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_vanishingCycles_red_eq_zero_and_add_le_finrank_span_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_forall_pow_eq_self_of_algEquiv
-- name    : AlgebraicCurve.exists_vanishingCycles_red_eq_zero_and_add_le_finrank_span_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_forall_pow_eq_self_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/ebeaa1e5-f227-557b-bee0-4467d1ed5f36
-- title:
--   Equivariant family of vanishing cycles of full rank
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A\subseteq L$ a valuation subring, $\pi\in A$ a nonzero element of the maximal ideal, and assume the rank-one condition `hrk`: for every $x\in L^\times$ and every $y$ in the maximal ideal of $A$ there is $n$ with $v(y^n)\le v(x)$. Let $F$ be a field extension of $L$ which is a curve over $L$ in the sense of `IsCurveOver` (principal divisors exist, residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type, and let $n,m$ be natural numbers. The combinatorial data are: fields $\bar F_i$ over the residue field of $A$ ($i\in\mathrm{Fin}\,n$) all of whose places are rational and which are themselves curves of `IsCurveOver` type; component charts $C_i$ (a valuation subring of $F$ with surjective residue map onto $\bar F_i$, a set of places `dom` all of which are rational, a finite set of nodes in $\bar F_i$, and a specialisation map `placeMap`); annuli $\mathrm{An}_e,\mathrm{An}'_e$ with source and target indices $\mathrm{src}\,e,\mathrm{tgt}\,e$ and attaching nodes $x^s_e,x^t_e$; weights $w_e$; and the hypotheses `hpair` (the two annuli of an edge have the same domain and the same nonzero modulus, and the product of their parameters is the image of that modulus), `hw` (the modulus is a unit times $\pi^{w_e}$), `hatt` ($\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x^s_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x^t_e$), `hnodes` (every node of every chart is the attaching point of exactly one of the $2m$ half-edges), `hcover` (each place of $F$ over $L$ lies in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain), `hdisc` (for each non-node place $Q$ of $\bar F_i$ there is an element $T$ of the chart's integers whose residue has order $1$ at $Q$, which is integral with residue in the maximal ideal at every place of the chart domain above $Q$, and which identifies the places of the chart domain above $Q$ bijectively with the elements of the maximal ideal of $A$ through $P\mapsto P.\mathrm{evalAt}\,T$), and the genus identity $g(F/L)+n=\sum_i g(\bar F_i)+m+1$. Further, $S$ is a set of semilinear automorphisms of $F$ over $L$ each of which, by `hS`, has base automorphism preserving $A$, fixing $\pi$ and inducing the identity on the residue field, preserves every chart and annulus domain, fixes the annulus parameters, preserves the charts' integers together with their residues, and commutes with `placeMap`; by `hSlift` every ring automorphism of $L$ with these three base properties is realised by a member of $S$. For a prime $\ell$ invertible in the residue field of $A$ it is assumed (`hSℓ`) that some $s\in S$ moves some $\ell$-th root $r$ of $\pi$, and that $V:=\mathbb{Q}_\ell\otimes_{\mathbb{Z}_\ell}T_\ell(\mathrm{Pic}^0(F/L))$ is finite-dimensional. Finally, `red` is a $\mathbb{Q}_\ell$-linear map from the $S$-invariants $V^S=\bigcap_{s\in S}\ker(\rho_\ell(s)-1)$ to $\prod_i\mathbb{Q}_\ell\otimes T_\ell(\mathrm{Pic}^0(\bar F_i))$ satisfying `hred`: whenever $v\in V^S$ is $1\otimes x$ with $x$ integral, the $k$-th projection of $x$ is the class of a degree-zero divisor $D=\sum_i D_i$ with each $D_i$ supported in $(C_i).\mathrm{dom}$ and of degree zero, then each component $\mathrm{red}\,v\,i$ is $1\otimes y$ for an integral Tate vector $y$ whose $k$-th projection is the class of the pushforward $\mathrm{mapDomain}\,(C_i).\mathrm{placeMap}\,D_i$. In addition a semistable model $M$ of $F$ over $A$ with this chart and annulus data and a descent datum $D$ for $M$ are given, and (`hκ`) if the residue field of $A$ has prime characteristic $p$ then each of its elements satisfies $a^{p^{n}}=a$ for some $n>0$. The conclusion is the existence of a family $vc:\mathrm{Fin}\,m\to V$ such that: each $vc_e$ lies in $V^S$ and is annihilated by `red`; $m+1\le\dim_{\mathbb{Q}_\ell}\operatorname{span}_{\mathbb{Q}_\ell}\{vc_e\}+n$; and the family is equivariant in the following sense: for every $L$-algebra automorphism $\tau$ of $F$ and permutations $\sigma_0$ of $\mathrm{Fin}\,n$, $\sigma_1$ of $\mathrm{Fin}\,m$ with $\mathrm{src}(\sigma_1e)=\sigma_0(\mathrm{src}\,e)$ and $\mathrm{tgt}(\sigma_1e)=\sigma_0(\mathrm{tgt}\,e)$, such that $\tau$ (acting through `SemilinearAut.ofAlgAut`) matches the chart domains $i$ with $\sigma_0 i$, the chart integers $i$ with $\sigma_0 i$ and the annulus domains $e$ with $\sigma_1 e$, and provided $\mathrm{src}\,e\ne\mathrm{tgt}\,e$ for all $e$, one has $\rho_\ell(\tau)(vc_e)=vc_{\sigma_1 e}$.
--
--   This produces the family of $\ell$-adic vanishing-cycle classes attached to the annuli of a semistable covering: classes inertia-invariant and killed by the chartwise reduction map, spanning a space of dimension at least $m+1-n$, and permuted by automorphisms of $F$ according to their action on the edges of the dual graph. It is the input to the comparison of the kernel of the reduction map with the span of the vanishing cycles, which is where the toric part of the $\ell$-adic representation attached to $\mathrm{Pic}^0$ is identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_vanishingCycles_red_eq_zero_and_add_le_finrank_span_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_forall_pow_eq_self_of_algEquiv.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem
    AlgebraicCurve.exists_vanishingCycles_red_eq_zero_and_add_le_finrank_span_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_forall_pow_eq_self_of_algEquiv
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    (red : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)) →ₗ[ℚ_[ℓ]]
      ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)))
    (hred : ∀ (v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)))
      (x : TateModule ℓ (Pic0 L F)), (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ (k : ℕ) (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x →
      ∀ Di : Fin n → Divisor L F, D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
          red v i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i),
            (E : Divisor (IsLocalRing.ResidueField A) (Fbar i)) =
                Finsupp.mapDomain (C i).placeMap (Di i) →
              TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = Pic0.mk E)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (hκ : ∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
      ∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ (p ^ n) = a)
    :
    ∃ vc : Fin m → ModularCurve.RationalTateModule ℓ (Pic0 L F),
      (∀ e, ∃ u : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)), (u : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = vc e ∧ red u = 0) ∧
      m + 1 ≤ Module.finrank ℚ_[ℓ] ↥(Submodule.span ℚ_[ℓ] (Set.range vc)) + n ∧
      ∀ (τ : F ≃ₐ[L] F) (σ₀ : Equiv.Perm (Fin n)) (σ₁ : Equiv.Perm (Fin m)),
        (∀ e, src (σ₁ e) = σ₀ (src e)) → (∀ e, tgt (σ₁ e) = σ₀ (tgt e)) →
        (∀ i, ∀ P : Place L F, P ∈ (C i).dom ↔ SemilinearAut.ofAlgAut τ • P ∈ (C (σ₀ i)).dom) →
        (∀ i, ∀ f : F, f ∈ (C i).integers ↔ τ f ∈ (C (σ₀ i)).integers) →
        (∀ e, ∀ P : Place L F, P ∈ (An e).dom ↔ SemilinearAut.ofAlgAut τ • P ∈ (An (σ₁ e)).dom) →
        (∀ e, src e ≠ tgt e) →
        ∀ e, ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) (SemilinearAut.ofAlgAut τ) (vc e) = vc (σ₁ e) := by sorry
